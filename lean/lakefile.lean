import Lake
open Lake DSL

package jsp_problem

-- Mathlib dependency placeholder; pin a reviewed commit/tag for reproducible work.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib JSPProblem

@[default_target]
lean_lib Main
