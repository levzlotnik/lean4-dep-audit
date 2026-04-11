import Lake
open Lake DSL

package UserProject where
  version := v!"0.1.0"

require MyLeanTermAuditor from ".." / ".."

lean_lib UserProject
