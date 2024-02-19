import Mathlib.Tactic.FunProp.ContDiff

/-!
# fun_prop configuration (about differentiability)
Additional mathlib lemmas which should be tagged @[fun_prop].

TODO: PR them to mathlib, to their appropriate files
-/

attribute [fun_prop] ContDiff.clm_apply
attribute [fun_prop] IsBoundedBilinearMap.contDiff
attribute [fun_prop] Differentiable.continuous
attribute [fun_prop] ContDiff.continuous
