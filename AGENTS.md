# AGENTS.md

## Developer Commands
- Build project: `lake build`
- Run executable: `lake exe myleantermauditor`

## Verification
- **Primary**: Check for Lean compiler diagnostics (errors/warnings) via LSP.
- **Logic Testing**: Add `#eval` blocks in `.lean` files (e.g., `Main.lean`) to verify auditor results during elaboration.
- **Build Check**: Run `lake build` to ensure no regressions in compilation.

## Architecture & Conventions
- **Core Logic**: `MyLeanTermAuditor/Audit.lean` implements the auditing logic for identifying axioms, opaque constants, and externs.
- **Execution Flow**: The tool is designed to run within the Lean elaboration context (`CommandElabM`) to access the `Environment`.
- **Sample Usage**: `Main.lean` demonstrates how to audit constants using `#eval`. Note that the compiled `main` function is currently a placeholder; actual audit results are observed during compilation/LSP analysis.
