import Mathlib.Topology.Algebra.Order.ProjIcc
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# fun_prop configuration (about continuity)
Additional mathlib lemmas which should be tagged @[fun_prop].

TODO: PR them to mathlib, to their appropriate files

-/

attribute [fun_prop] continuous_projIcc

-- xxx: is this a good lemma? used in `orthogonalProjectionOrthogonalLineIso`
attribute [fun_prop] Continuous.subtype_val
attribute [fun_prop] Continuous.div_const
attribute [fun_prop] continuous_snd

attribute [fun_prop] Continuous.inner
attribute [fun_prop] Metric.continuous_infDist_pt
