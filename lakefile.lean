import Lake
open Lake DSL

package MyLeanTermAuditor where
  version := v!"0.1.0"

require FfiFixture from "test-packages" / "ffi-fixture"

lean_lib MyLeanTermAuditor

lean_lib TestFixtures

lean_lib Tests where
  globs := #[.submodules `Tests]

/-- Demos: #audit command examples. Build with `lake build demo`. -/
lean_exe demo where
  root := `Demo

/-- CLI: `lake exe audit <const> --import <module> [--config standard|full|...]` -/
@[default_target]
lean_exe audit where
  root := `Main

/-- CLI integration tests. Run with `lake build test_cli && lake exe test_cli`. -/
lean_exe test_cli where
  root := `TestCLI
