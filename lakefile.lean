import Lake
open Lake DSL

package «SphereEversion» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"YK-homeomorph-unit-ball"

@[default_target]
lean_lib «SphereEversion» {
  -- add any library configuration options here
}
