import analysis.normed_space.basic
import algebra.support

/-
This file should be split between the topology and the analysis folders.
-/

open function set 

variables {X α : Type*} [has_zero α]

lemma support_empty_iff {f : X → α} : support f = ∅ ↔ ∀ x, f x = 0 :=
by simp_rw [← nmem_support, eq_empty_iff_forall_not_mem]

variables [topological_space X]

/-- The topological support of a function, is the closure of its support. -/
def tsupport (f : X → α) : set X := closure (support f)

lemma support_subset_tsupport (f : X → α) : support f ⊆ tsupport f :=
subset_closure

lemma tsupport_empty_iff {f : X → α} : tsupport f = ∅ ↔ ∀ x, f x = 0 :=
by erw [closure_empty_iff, support_empty_iff]

lemma image_eq_zero_of_nmem_tsupport {f : X → α} {x : X} (hx : x ∉ tsupport f) : f x = 0 :=
support_subset_iff'.mp (support_subset_tsupport f) x hx

variables {E : Type*} [normed_group E]

lemma continuous.bounded_of_vanishing_outside_compact {f : X → E} (hf : continuous f)
  {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
begin
  rcases eq_empty_or_nonempty K with h|h,
  { use 0,
    simp [h, hfK, le_refl] },
  { obtain ⟨x, x_in, hx⟩ : ∃ x ∈ K, ∀ y ∈ K, ∥f y∥ ≤ ∥f x∥ :=
      hK.exists_forall_ge h (continuous_norm.comp hf).continuous_on,
    use ∥f x∥,
    intros y,
    by_cases hy : y ∈ K,
    { exact hx y hy },
    { simp [hfK y hy] } }
end

lemma continuous.bounded_of_compact_support {f : X → E} (hf : continuous f)
  (hsupp : is_compact (tsupport f)) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
hf.bounded_of_vanishing_outside_compact hsupp (λ x, image_eq_zero_of_nmem_tsupport)