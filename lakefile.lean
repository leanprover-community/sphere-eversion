import Lake
open Lake DSL

package «SphereEversion» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SphereEversion» where
