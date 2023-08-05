import Lake
open Lake DSL

package «nederpelt» {
  -- add package configuration options here
}

lean_lib «Nederpelt» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ab4ba6c49d41daca175dc9bbeb5f493ece93c2f6"

@[default_target]
lean_exe «nederpelt» {
  root := `Main
}
