import analysis.normed_space.basic
import algebra.support

/-
This file should be split between the topology and the analysis folders.
-/

open function set filter
open_locale pointwise topological_space

variables {X α α' β γ δ M E : Type*}

section order

variables [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β]
variables [topological_space X] [normed_group E]


/-! below: still to move -/

@[simp] lemma set.range_coe {α} {s : set α} : range (coe : s → α) = s :=
subtype.range_coe_subtype

lemma le_csupr_set {ι α} [conditionally_complete_lattice α] {f : ι → α} {s : set ι}
  (H : bdd_above (f '' s)) {c : ι} (hc : c ∈ s) : f c ≤ ⨆ i : s, f i :=
le_csupr (by simp_rw [range_comp f, set.range_coe, H] : bdd_above $ range (λ i : s, f i)) ⟨c, hc⟩

-- lemma is_compact.bdd_above_range_set {f : β → α} {K : set β} (hK : is_compact K)
--   (hf : continuous_on f K) {x : β} (hx : x ∈ K) : f x ≤ ⨆ x' : K, f x' :=
-- le_csupr_set (hK.bdd_above_image hf.continuous_on) hx

-- lemma continuous.le_csupr_subtype {f : β → α} (hf : continuous f) {K : set β} (hK : is_compact K)
--   {x : β} (hx : x ∈ K) : f x ≤ ⨆ x' : K, f x' :=
-- le_csupr (by simp_rw [range_comp f, set.range_coe, hK.bdd_above_image hf.continuous_on] :
--   bdd_above $ range (λ x' : K, f x')) (⟨x, hx⟩ : K)

@[to_additive]
def homeomorph.div_left {G} [topological_space G] [group G] [topological_group G] (x : G) :
   G ≃ₜ G :=
{ continuous_to_fun := continuous_const.div' continuous_id,
  continuous_inv_fun := continuous_inv.mul continuous_const,
  .. equiv.div_left x }

@[to_additive]
def homeomorph.div_right {G} [topological_space G] [group G] [topological_group G] (x : G) :
   G ≃ₜ G :=
{ continuous_to_fun := continuous_id.div' continuous_const,
  continuous_inv_fun := continuous_id.mul continuous_const,
  .. equiv.div_right x }

end order
