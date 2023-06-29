import analysis.convex.basic
import algebra.module.big_operators

open_locale big_operators
open function

variables (𝕜 : Type*) {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
  [module 𝕜 E] -- note to Patrick: I needed this at some point



def really_convex_hull (𝕜 : Type*) {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
  [has_smul 𝕜 E] (s : set E) : set E :=
{e | ∃ w : E → 𝕜,  0 ≤ w ∧ support w ⊆ s ∧ ∑ᶠ x, w x = 1 ∧ e = ∑ᶠ x, w x • x}

variable {𝕜}

-- https://xkcd.com/927/
lemma finsum.exists_ne_zero_of_sum_ne_zero {β α : Type*} {s : finset α} {f : α → β}
  [add_comm_monoid β] : ∑ᶠ x ∈ s, f x ≠ 0 → (∃ (a : α) (H : a ∈ s), f a ≠ 0) :=
begin
  rw finsum_mem_finset_eq_sum,
  exact finset.exists_ne_zero_of_sum_ne_zero,
end

@[to_additive]
lemma finite_of_finprod_ne_one {M : Type*} {ι : Sort*} [comm_monoid M] {f : ι → M}
  (h : ∏ᶠ i, f i ≠ 1) : (mul_support f).finite :=
begin
  classical,
  rw finprod_def at h,
  contrapose h,
  rw [not_not, dif_neg h]
end

lemma foo {α β M : Type*} [add_comm_monoid M] (f : β → α) (s : finset β) [decidable_eq α]
  (g : β → M) :
  ∑ᶠ (x : α), ∑ (y : β) in finset.filter (λ (j : β), f j = x) s, g y = ∑ k in s, g k :=
begin
  rw finsum_eq_finset_sum_of_support_subset _ (show _ ⊆ ↑(s.image f), from _),
  { rw finset.sum_image',
    intros,
    refl, },
  { intros x hx,
    rw mem_support at hx,
    obtain ⟨a, h, ha⟩ := finset.exists_ne_zero_of_sum_ne_zero hx,
    simp at ⊢ h,
    exact ⟨a, h⟩,
  },
end

lemma sum_mem_really_convex_hull {s : set E} {ι : Type*} {t : finset ι} {w : ι → 𝕜}
  {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ really_convex_hull 𝕜 s :=
begin
  classical,
  refine ⟨λ e, (∑ᶠ i ∈ t.filter (λ j, z j = e), w i), _, _, _, _⟩,
  { rw pi.le_def,
    intro e,
    apply finsum_nonneg (λ i, _),
    exact finsum_nonneg (λ hi, h₀ _ (finset.mem_of_mem_filter i hi)), },
  { intros e he,
    rw mem_support at he,
    obtain ⟨a, h, ha⟩ := finsum.exists_ne_zero_of_sum_ne_zero he,
    rw finset.mem_filter at h,
    rcases h with ⟨h, rfl⟩,
    exact hz a h, },
  { rw ← h₁,
    simp_rw finsum_mem_finset_eq_sum,
    rw foo z _ _, },
  { simp_rw [finsum_mem_finset_eq_sum, finset.sum_smul],
    rw ← foo z,
    congr',
    ext x,
    rw finset.sum_congr rfl,
    intros y hy,
    rw finset.mem_filter at hy,
    rw hy.2, },
end

lemma really_convex_hull_mono : monotone (really_convex_hull 𝕜 : set E → set E) :=
begin
  rintros s t h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩,
  exact ⟨w, w_pos, supp_w.trans h, sum_w, rfl⟩
end

def really_convex (𝕜 : Type*) {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
  [module 𝕜 E] (s : set E) : Prop :=
  ∀ w : E → 𝕜,  0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s

variables {s : set E}

lemma really_convex_iff_hull : really_convex 𝕜 s ↔ really_convex_hull 𝕜 s ⊆ s :=
begin
  split,
  { rintros h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩,
    exact h w w_pos supp_w sum_w },
  { rintros h w w_pos supp_w sum_w,
    exact h ⟨w, w_pos, supp_w, sum_w, rfl⟩ }
end

lemma really_convex.sum_mem (hs : really_convex 𝕜 s) {ι : Type*} {t : finset ι} {w : ι → 𝕜}
  {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
really_convex_iff_hull.mp hs (sum_mem_really_convex_hull h₀ h₁ hz)

lemma really_convex.inter {t : set E} (hs : really_convex 𝕜 s) (ht : really_convex 𝕜 t) :
  really_convex 𝕜 (s ∩ t) :=
begin
  intros w w_pos supp_w sum_w,
  cases set.subset_inter_iff.mp supp_w,
  split,
  { apply hs ; assumption },
  { apply ht ; assumption }
end


/-  The next lemma would also be nice to have.
lemma really_convex_really_convex_hull (s : set E) : really_convex 𝕜 (really_convex_hull 𝕜 s) :=
sorry
 -/
