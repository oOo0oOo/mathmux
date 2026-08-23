import Lake

open Lake DSL

package mathmux

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "f2916a54665af851fc9a4da901cfc242c47a8922"

@[default_target]
lean_lib MathmuxFixture
