/-
  ExternSourceProvenance: IO-based post-processing that traces @[extern] symbols
  back to their C source files through Lake's build trace files.

  Runs AFTER the pure audit pass and AFTER resolveLocations.
-/
import Lean
import Lean4DepAudit.Types

open Lean System

namespace Lean4DepAudit



-- ============================================================================
-- Step 1: `nm` wrapper
-- ============================================================================

/-- Run `nm --defined-only` on a library file and return the set of defined symbol names. -/
def nmDefinedSymbols (libPath : FilePath) : IO (Std.HashSet String) := do
  let result ← try
    IO.Process.output { cmd := "nm", args := #["--defined-only", libPath.toString] }
  catch _ =>
    return {}
  if result.exitCode != 0 then return {}
  let mut symbols : Std.HashSet String := {}
  for line in result.stdout.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    let parts := trimmed.splitOn " "
    -- Lines look like: "0000000000001234 T symbol_name"
    -- or on some systems: "T symbol_name" (for object files)
    -- We want the last field if the second-to-last is a single letter
    if parts.length >= 3 then
      let typeLetter := parts[1]!
      let symName := parts[2]!
      if typeLetter.length == 1 && !symName.isEmpty then
        symbols := symbols.insert symName
    else if parts.length == 2 then
      let typeLetter := parts[0]!
      let symName := parts[1]!
      if typeLetter.length == 1 && !symName.isEmpty then
        symbols := symbols.insert symName
  return symbols

-- ============================================================================
-- Step 2: Trace file parsing
-- ============================================================================

/-- Extract file paths from a JSON value representing trace inputs.
    Inputs can be flat (["path", "hash"]) or nested (["caption", [["path", "hash"], ...]]).
    Returns all file paths found at any nesting level. -/
private partial def extractInputPaths (inputs : Json) : Array String :=
  go inputs #[]
where
  go (j : Json) (acc : Array String) : Array String :=
    match j with
    | .arr elems =>
      elems.foldl (init := acc) fun acc elem =>
        match elem with
        | .arr pair =>
          if pair.size >= 2 then
            match pair[0]!, pair[1]! with
            | .str caption, .str _ =>
              -- Flat input: ["path", "hash"]
              acc.push caption
            | .str _, .arr nested =>
              -- Nested input: ["caption", [["path", "hash"], ...]]
              go (.arr nested) acc
            | _, _ => acc
          else acc
        | _ => acc
    | _ => acc

/-- Parse a .trace JSON file and extract input file paths from the "inputs" array.
    Inputs can be flat (["path", "hash"]) or nested (["caption", [["path", "hash"], ...]]).
    Returns all file paths found at any nesting level. -/
def parseTraceInputPaths (tracePath : FilePath) : IO (Array String) := do
  let contents ← try IO.FS.readFile tracePath catch _ => return #[]
  let json ← match Json.parse contents with
    | .ok j => pure j
    | .error _ => return #[]
  match json.getObjVal? "inputs" with
  | .ok inputs => return extractInputPaths inputs
  | .error _ => return #[]

/-- Given a .a file path, find the .o files that were archived into it by reading its .trace file. -/
def traceStaticLibInputs (aFile : FilePath) : IO (Array String) := do
  let tracePath : FilePath := aFile.toString ++ ".trace"
  let allPaths ← parseTraceInputPaths tracePath
  return allPaths.filter fun p => p.endsWith ".o"

/-- Given a .o file path, find the .c source file that was compiled into it by reading its .trace file. -/
def traceObjectInput (oFile : FilePath) : IO (Option String) := do
  let tracePath : FilePath := oFile.toString ++ ".trace"
  let allPaths ← parseTraceInputPaths tracePath
  return allPaths.find? fun p => p.endsWith ".c" || p.endsWith ".cpp" || p.endsWith ".cc"

-- ============================================================================
-- Step 3: lean.h static inline scanner
-- ============================================================================

/-- Check if a symbol is declared as `static inline` in lean.h.
    Reads the lean.h file and checks for lines containing both `static inline` and the symbol. -/
def isStaticInlineInHeader (sysroot : FilePath) (symbol : String) : IO Bool := do
  let headerPath := sysroot / "include" / "lean" / "lean.h"
  let contents ← try IO.FS.readFile headerPath catch _ => return false
  for line in contents.splitOn "\n" do
    if line.hasSubstr "static inline" && line.hasSubstr symbol then
      return true
  return false

-- ============================================================================
-- Step 4: Build the symbol → library index
-- ============================================================================

/-- List all .a files in a directory. Returns empty if directory doesn't exist. -/
private def listStaticLibs (dir : FilePath) : IO (Array FilePath) := do
  try
    let mut result : Array FilePath := #[]
    let dirEntries ← dir.readDir
    for entry in dirEntries do
      if entry.fileName.endsWith ".a" then
        result := result.push entry.path
    return result
  catch _ => return #[]

/-- Scan all .a files in a directory and build a symbol → library path map. -/
def indexLibrarySymbols (dir : FilePath) : IO (Std.HashMap String FilePath) := do
  let libs ← listStaticLibs dir
  let mut index : Std.HashMap String FilePath := {}
  for lib in libs do
    let syms ← nmDefinedSymbols lib
    for sym in syms do
      -- First one wins
      if !index.contains sym then
        index := index.insert sym lib
  return index

-- ============================================================================
-- Step 4b: Harvest linked libraries from trace files
-- TODO: 'binaryOnly' edge case is in review, this is placeholder
-- ============================================================================

-- /-- Scan `.trace` files in the given directories to discover additional `.a` files
--     referenced as link inputs (e.g. from `input_file` + `moreLinkObjs`).
--     Returns deduplicated paths to `.a` files that actually exist on disk. -/
-- private def harvestLinkedLibraries (dirs : Array FilePath) : IO (Array FilePath) := do
--   let mut seen : Std.HashSet String := {}
--   let mut result : Array FilePath := #[]
--   for dir in dirs do
--     let entries ← try dir.readDir catch _ => pure #[]
--     for entry in entries do
--       if entry.fileName.endsWith ".trace" then
--         let inputPaths ← parseTraceInputPaths entry.path
--         for p in inputPaths do
--           if p.endsWith ".a" && !seen.contains p then
--             let fp : FilePath := p
--             if ← fp.pathExists then
--               seen := seen.insert p
--               result := result.push fp
--   return result

-- ============================================================================
-- Step 5: Full source chain tracing
-- ============================================================================

/-- Trace an extern symbol from a .a file back to its C source.
    Follows: .a.trace → .o paths → .o.trace → .c path → check .c exists. -/
def traceSymbolToSource (aFile : FilePath) (symbol : String) : IO (Option SymbolProvenance) := do
  -- Step 1: Read .a.trace → get .o file paths
  let oFiles ← traceStaticLibInputs aFile
  if oFiles.isEmpty then return none
  -- Step 2: For each .o file, run nm to check if it contains the symbol
  for oFileStr in oFiles do
    let oFile : FilePath := oFileStr
    let syms ← nmDefinedSymbols oFile
    if syms.contains symbol then
      -- Step 3: Read .o.trace → get .c path
      match ← traceObjectInput oFile with
      | some cFileStr =>
        -- Step 4: Check the .c file exists on disk
        let cFile : FilePath := cFileStr
        let exists_ ← cFile.pathExists
        if exists_ then
          return some (.tracedToSource cFileStr oFileStr aFile.toString)
      | none => pure ()
  return none

-- ============================================================================
-- Step 6: Toolchain lib detection helpers
-- ============================================================================

/-- Check if a path looks like it's in the Lean toolchain directory. -/
private def isToolchainPath (sysroot : FilePath) (p : FilePath) : Bool :=
  p.toString.startsWith sysroot.toString

-- ============================================================================
-- Step 7: Main resolution function
-- ============================================================================

/-- Resolve provenance for all extern findings in an audit result.
    Scans .a files in search paths, traces symbols to C source via Lake trace files.
    Falls back to toolchain runtime / lean.h header / unresolved. -/
def resolveProvenance (result : AuditResult) (searchPath : Lean.SearchPath) : IO AuditResult := do
  let sysroot ← try Lean.findSysroot catch _ => return result
  -- Compute library directories to scan
  let mut libDirs : Array FilePath := #[]
  for entry in searchPath do
    -- The search path entry itself (e.g. .lake/build/lib/lean)
    libDirs := libDirs.push entry
    -- Parent directory (e.g. .lake/build/lib/) where .a files for extern_lib live
    match entry.parent with
    | some parent => libDirs := libDirs.push parent
    | none => pure ()
  -- Also add the toolchain's lib/lean directory for libleanrt.a
  let toolchainLibDir := sysroot / "lib" / "lean"
  libDirs := libDirs.push toolchainLibDir
  -- Deduplicate
  let mut seen : Std.HashSet String := {}
  let mut uniqueDirs : Array FilePath := #[]
  for d in libDirs do
    let s := d.toString
    if !seen.contains s then
      seen := seen.insert s
      uniqueDirs := uniqueDirs.push d
  -- Build symbol index from all .a files in those directories
  let mut symbolIndex : Std.HashMap String FilePath := {}
  for dir in uniqueDirs do
    let dirIndex ← indexLibrarySymbols dir
    for (sym, lib) in dirIndex do
      if !symbolIndex.contains sym then
        symbolIndex := symbolIndex.insert sym lib
  -- TODO: 'binaryOnly' edge case is in review, this is placeholder
  -- Harvest additional .a files referenced in trace files (e.g. input_file + moreLinkObjs)
  -- let harvestedLibs ← harvestLinkedLibraries uniqueDirs
  -- for aFile in harvestedLibs do
  --   let alreadyIndexed := uniqueDirs.any fun d => aFile.toString.startsWith (d.toString ++ "/")
  --   if !alreadyIndexed then
  --     let syms ← nmDefinedSymbols aFile
  --     for sym in syms do
  --       if !symbolIndex.contains sym then
  --         symbolIndex := symbolIndex.insert sym aFile
  -- Process each extern finding
  let mut findings := result.findings
  let findingsArr := result.findingsArray
  for fi in findingsArr do
    match fi.finding with
    | .extern_ sym =>
      let provenance ← do
        match symbolIndex[sym]? with
        | some aFile =>
          if isToolchainPath sysroot aFile then
            -- Found in toolchain library
            pure (SymbolProvenance.toolchainRuntime aFile.toString)
          else
            -- Try to trace through build artifacts
            match ← traceSymbolToSource aFile sym with
            | some prov => pure prov
            | none =>
              -- TODO: 'binaryOnly' edge case is in review, this is placeholder
              -- Previously: pure (SymbolProvenance.binaryOnly aFile.toString)
              pure SymbolProvenance.unresolved
        | none =>
          -- Not found in any .a — check if it's a static inline in lean.h
          if ← isStaticInlineInHeader sysroot sym then
            pure SymbolProvenance.toolchainHeader
          else
            pure SymbolProvenance.unresolved
      let updatedFi := { fi with provenance? := some provenance }
      findings := findings.insert fi.name updatedFi
    | _ => pure ()  -- Skip non-extern findings
  return { result with findings }

end Lean4DepAudit
