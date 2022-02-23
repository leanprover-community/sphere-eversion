import analysis.normed_space.basic
import algebra.support

/-
This file should be split between the topology and the analysis folders.
-/

open function set filter
open_locale pointwise topological_space

variables {X α α' β γ δ M E : Type*}

section monoid

variables [topological_space α] [monoid_with_zero β] [add_monoid γ] [distrib_mul_action β γ]
variables {f : α → β} {f' : α → γ} {x : α}

lemma has_compact_support.smul (hf : has_compact_support f)
  (hf' : has_compact_support f') : has_compact_support (f • f') :=
by apply hf.comp₂_left hf' (smul_zero 0) -- `by apply` speeds up elaboration

end monoid

section monoid_with_zero

variables [topological_space α] [mul_zero_class β]
variables {f f' : α → β} {x : α}

@[to_additive]
lemma has_compact_support.mul (hf : has_compact_support f)
  (hf' : has_compact_support f') : has_compact_support (f * f') :=
by apply hf.comp₂_left hf' (mul_zero 0) -- `by apply` speeds up elaboration

end monoid_with_zero

section order

variables [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β]

-- topology.algebra.ordered.compact

-- better proof
lemma continuous.exists_forall_le'' [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_top) :
  ∃ x, ∀ y, f x ≤ f y :=
by { inhabit β, exact hf.exists_forall_le' default (hlim.eventually $ eventually_ge_at_top _) }



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
