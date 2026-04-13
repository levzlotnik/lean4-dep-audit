# lean4-dep-audit

A Lean 4 dependency auditor that goes beyond `#print axioms`. Traverses all
transitive dependencies of a constant and classifies every axiom, opaque, and
`@[extern]` FFI binding it finds -- then traces extern symbols back to their C
source through Lake's build artifacts and checks that the C function signatures
match the Lean FFI ABI.

Built on Lean 4 v4.29.0. No Mathlib dependency.

## What It Does

| Feature | `#print axioms` | **This tool** |
|---|---|---|
| List axioms | Yes | Yes |
| Classify opaques (partial, implementedBy, initialize) | No | Yes |
| Detect `@[extern]` FFI bindings | No | Yes |
| Runtime vs kernel-time reachability | No | Yes |
| Trace extern symbols to C source files | No | Yes |
| Check C function signatures against Lean FFI ABI | No | Yes |
| Drill-down: "why does X depend on Y?" | No | Yes |
| Configurable trust boundaries / filter DSL | No | Yes |
| JSON output for tooling | No | Yes |

## Quick Start

```bash
# Build the CLI (default target)
lake build

# Audit a constant
lake exe audit IO.println --import Init

# Audit with the standard config (filters out known-safe stdlib internals)
lake exe audit myMain --import MyModule --config standard

# Drill-down: "why does myMain depend on this extern?"
lake exe audit myMain --import MyModule --drill Array.size

# JSON output
lake exe audit myMain --import MyModule --format json
```

### In-editor `#audit` command

```lean
import Lean4DepAudit

#audit myMain                                          -- standard config
#audit myMain with AuditConfig.runtimeExterns          -- runtime externs only
#audit myMain with AuditConfig.default                 -- full audit (everything)
#audit myMain with { drill := [`propext] }             -- drill-down
#audit (myMain, otherMain)                             -- multiple constants
```

## Example Output

### Auditing a function with real FFI bindings

```
$ lake exe audit FfiFixture.callsBothFfi --import FfiFixture
```

```yaml
audited:
  - FfiFixture.callsBothFfi
visited: 6
findings:
  - name: FfiFixture.ffiAdd
    kind: extern "test_ffi_add"
    type: "UInt32 → UInt32 → UInt32"
    reachability: runtime
    location: "FfiFixture.Basic:3:0"
    encounters: 1
    provenance: traced ".../test-packages/ffi-fixture/c/ffi.c:13"
    type-check: compatible
  - name: FfiFixture.ffiToggle
    kind: extern "test_ffi_toggle"
    type: "Bool → Bool"
    reachability: runtime
    location: "FfiFixture.Basic:7:0"
    encounters: 1
    provenance: traced ".../test-packages/ffi-fixture/c/ffi.c:19"
    type-check: compatible
```

Every extern finding includes:
- **provenance** -- where the native code lives: `traced` (full chain to `.c` file),
  `toolchain-runtime` (in `libleanrt.a`), `toolchain-header` (`static inline` in `lean.h`),
  or `UNRESOLVED` (no native backing found -- suspicious)
- **type-check** -- whether the C function signature matches what the Lean FFI ABI expects

### Drill-down: "why does X depend on Y?"

```
$ lake exe audit FfiFixture.ffiChainRoot --import FfiFixture --drill FfiFixture.ffiAdd
```

```yaml
audited:
  - FfiFixture.ffiChainRoot
visited: 11
findings:
  - name: FfiFixture.ffiConst42
    kind: extern "test_ffi_const42"
    type: "Unit → UInt32"
    reachability: runtime
    location: "FfiFixture.Basic:11:0"
    encounters: 1
    provenance: traced ".../test-packages/ffi-fixture/c/ffi.c:25"
    type-check: compatible
  - name: FfiFixture.ffiAdd
    kind: extern "test_ffi_add"
    type: "UInt32 → UInt32 → UInt32"
    reachability: runtime
    location: "FfiFixture.Basic:3:0"
    encounters: 1
    provenance: traced ".../test-packages/ffi-fixture/c/ffi.c:13"
    type-check: compatible
drill:
  - from: FfiFixture.ffiChainRoot
    target: FfiFixture.ffiAdd
    children:
      - FfiFixture.callsFfiAdd
```

The drill answers: "which *direct* dependencies of `ffiChainRoot` are on the path
to `ffiAdd`?" Answer: `callsFfiAdd`.

### Filter DSL

```bash
# Only externs reachable at runtime
lake exe audit myMain --import MyModule --report 'externs & runtime'

# Non-standard axioms only (excludes propext, Quot.sound, Classical.choice)
lake exe audit myMain --import MyModule --report 'nonStdAxioms'

# Everything except stdlib, skip descending into proof terms
lake exe audit myMain --import MyModule --report '!stdlib' --descend skipProofs
```

## Architecture

Two-pass design:

```
Environment
    |
    v
auditConst (pure)  -->  AuditResult { findings, visited, reverseDeps }
    |                         |
    |                         v
    |                    resolveLocations (MetaM, optional)
    |                         |
    |                         v
    |                    resolveProvenance (IO, optional)
    |                         |         nm .a -> parse .trace -> find .c
    |                         v
    |                    resolveTypeAudit (IO + MetaM, optional)
    |                         |         parse C sig -> compare with Lean type
    |                         v
    v                    AuditResult (enriched)
drillDown (pure)  <--        |
    |                        |
    v                        v
DrillResult              output (YAML / JSON)
```

**Pass 1 (`auditConst`):** `Environment -> AuditConfig -> Name -> AuditResult`.
Walks all reachable constants via `Expr.foldConsts`, classifies findings, records
reachability flags, builds a reverse dependency DAG. Handles 4,300+ constants
for a typical `IO Unit` program.

**Pass 2 (`drillDown`):** `Environment -> Name -> Name -> AuditResult -> DrillResult`.
Answers "which direct deps of X lead to target Y?" via BFS ancestor set +
immediate dependency intersection on the pre-computed DAG.

**Post-processing (optional):**
- `resolveLocations` -- fills in source locations and pretty-printed types
- `resolveProvenance` -- traces extern symbols through Lake build artifacts:
  `.a` -> `.a.trace` -> `.o` -> `.o.trace` -> `.c` (runs `nm`)
- `resolveTypeAudit` -- parses C function signatures and checks compatibility
  with the Lean FFI ABI

## Tests

**69 tests. All passing.**

- **38 unit tests** (`lake build Tests`) -- `run_cmd` blocks that fail the build
  on assertion failure. Cover axiom/extern/opaque detection, drill-down, multi-constant
  audits, type info, and all 4 provenance classifications.
- **31 CLI integration tests** (`lake build test_cli && lake exe test_cli`) --
  shell out to the compiled CLI, check YAML substring matching and JSON
  round-trip deserialization.
- **Real FFI test fixture** -- a separate Lake package (`test-packages/ffi-fixture/`)
  with C source compiled via `extern_lib`, exercising the full provenance chain
  from Lean `@[extern]` through `nm` to the `.c` file.

```bash
lake build Tests                              # unit tests
lake build audit && lake build test_cli && lake exe test_cli  # CLI tests
```

## Known Limitations

- **Interpreter bottleneck:** The `#audit` elaborator command runs in the Lean
  interpreter, which is ~100x slower than compiled code. The CLI (`lake exe audit`)
  is the fast path. `set_option profiler true` on the `#audit` demos shows ~55s
  interpretation for `IO Unit` constants.
- **C parser is intentionally simple:** The C signature parser in `ExternCAudit.lean`
  is a hand-rolled tokenizer. If it can't parse a signature cleanly, *that is the finding*
  -- it reports `unparseable` rather than guessing.
- **`binaryOnly` provenance is shelved:** Some extern symbols exist only in `.a`
  files with no traceable `.c` source (e.g., Lean compiler-generated code). The
  classification for this case is deferred pending investigation with the Lake team.
- **`ExprPath` / stack traces are dormant:** Types and formatters for expression-level
  path tracking exist but are not wired into either pass. Reserved for a future
  targeted path collection pass.

## Project Structure

```
Lean4DepAudit/
  Types.lean                 -- Core data types + JSON serialization
  Classify.lean              -- Constant classification (axiom/opaque/extern)
  Traverse.lean              -- Pass 1 (pure traversal) + Pass 2 (drill-down)
  Filter.lean                -- Composable filter predicates + preset configs
  ExternSourceProvenance.lean -- Trace extern symbols to C source via Lake artifacts
  ExternCAudit.lean          -- C type parser + Lean FFI ABI compatibility checker
  Command.lean               -- #audit elaborator command
  CLI.lean                   -- CLI executable + filter DSL parser
  Monad.lean                 -- Thin orchestration monad (StateT AuditResult MetaM)
  StackTrace.lean            -- Expression path formatting (dormant)
Main.lean                    -- CLI entry point
Demo.lean                    -- #audit command examples
TestFixtures/                -- Constants with known audit properties
Tests/                       -- 38 unit tests
TestCLI.lean                 -- 31 CLI integration tests
test-packages/
  ffi-fixture/               -- Real extern_lib package with C source
  user-project/              -- Downstream consumer simulation for CLI tests
```

## License

MIT. See [LICENSE](LICENSE).
