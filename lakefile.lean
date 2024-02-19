import Lake
open Lake DSL

package «SphereEversion» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "lecopivo/fun_prop_refactor"

@[default_target]
lean_lib «SphereEversion» where
