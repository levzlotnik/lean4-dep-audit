import Lake
open Lake DSL

package MyLeanTermAuditor where
  version := v!"0.1.0"

require FfiFixture from "test-packages" / "ffi-fixture"

lean_lib MyLeanTermAuditor

lean_lib TestFixtures

lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe myleantermauditor where
  root := `Main
