import Mathlib.Tactic.FunProp.Continuous

import Mathlib.Topology.Algebra.Order.ProjIcc
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# fun_prop configuration
Additional mathlib lemmas which should be tagged @[fun_prop].

TODO: PR them to mathlib, to avoid this "kitchen sink" file.
-/

attribute [fun_prop] continuous_projIcc

attribute [fun_prop] Continuous.prod_map
-- xxx: is this a good lemma? used in `orthogonalProjectionOrthogonalLineIso`
attribute [fun_prop] Continuous.subtype_val
attribute [fun_prop] Continuous.comp₃
attribute [fun_prop] Continuous.div_const
attribute [fun_prop] continuous_snd

attribute [fun_prop] Continuous.inner
attribute [fun_prop] Metric.continuous_infDist_pt
