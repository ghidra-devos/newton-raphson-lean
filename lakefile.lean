import Lake
open Lake DSL

package «newton-raphson» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib «NewtonRaphson» where
