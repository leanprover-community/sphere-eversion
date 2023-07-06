import analysis.convex.combination
import algebra.module.big_operators
import algebra.order.hom.ring

open_locale big_operators
open function set

-- move

lemma map_finsum {β α γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] {G : Type*}
  [add_monoid_hom_class G β γ] (g : G) {f : α → β} (hf : (function.support f).finite) :
  g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
(g : β →+ γ).map_finsum hf

@[to_additive] lemma finprod_eq_prod_of_mul_support_subset_of_finite {α M} [comm_monoid M]
  (f : α → M) {s : set α} (h : mul_support f ⊆ s) (hs : s.finite) :
  ∏ᶠ i, f i = ∏ i in hs.to_finset, f i :=
by { apply finprod_eq_prod_of_mul_support_subset f, rwa [set.finite.coe_to_finset] }

-- end move
section
variables {𝕜 𝕜' : Type*} {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  {E₂ : Type*} [add_comm_monoid E₂] [module 𝕜 E₂]
  {E' : Type*} [add_comm_monoid E'] [ordered_semiring 𝕜'] [module 𝕜' E']
  (σ : 𝕜 →+*o 𝕜')

def really_convex_hull (𝕜 : Type*) {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
  [has_smul 𝕜 E] (s : set E) : set E :=
{e | ∃ w : E → 𝕜, 0 ≤ w ∧ support w ⊆ s ∧ ∑ᶠ x, w x = 1 ∧ e = ∑ᶠ x, w x • x}

-- https://xkcd.com/927/
lemma finsum.exists_ne_zero_of_sum_ne_zero {β α : Type*} {s : finset α} {f : α → β}
  [add_comm_monoid β] : ∑ᶠ x ∈ s, f x ≠ 0 → (∃ (a : α) (H : a ∈ s), f a ≠ 0) :=
begin
  rw finsum_mem_finset_eq_sum,
  exact finset.exists_ne_zero_of_sum_ne_zero,
end

-- rename: `mul_support_finite_of_finprod_ne_one`?
@[to_additive]
lemma finite_of_finprod_ne_one {M : Type*} {ι : Sort*} [comm_monoid M] {f : ι → M}
  (h : ∏ᶠ i, f i ≠ 1) : (mul_support f).finite :=
begin
  classical,
  rw finprod_def at h,
  contrapose h,
  rw [not_not, dif_neg h]
end

lemma support_finite_of_finsum_eq_of_ne_zero {M : Type*} {ι : Sort*} [add_comm_monoid M] {f : ι → M}
  {x : M} [ne_zero x] (h : ∑ᶠ i, f i = x) : (support f).finite :=
begin
  apply finite_of_finsum_ne_zero,
  rw [h],
  apply ne_zero.ne,
end

@[to_additive]
lemma subsingleton.mul_support_eq {α β} [subsingleton β] [has_one β] (f : α → β) :
  mul_support f = ∅ :=
by { rw [mul_support_eq_empty_iff], ext, apply subsingleton.elim }

lemma support_finite_of_finsum_eq_one {M : Type*} {ι : Sort*} [non_assoc_semiring M] {f : ι → M}
  (h : ∑ᶠ i, f i = 1) : (support f).finite :=
begin
  casesI subsingleton_or_nontrivial M,
  { simp_rw [subsingleton.support_eq, finite_empty] },
  exact support_finite_of_finsum_eq_of_ne_zero h
end

lemma finsum_sum_filter {α β M : Type*} [add_comm_monoid M] (f : β → α) (s : finset β)
  [decidable_eq α] (g : β → M) :
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
    rw finsum_sum_filter z _ _, },
  { simp_rw [finsum_mem_finset_eq_sum, finset.sum_smul],
    rw ← finsum_sum_filter z,
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

/-- Generalization of `convex` to semirings. We only add the `s = ∅` clause if `𝕜` is trivial. -/
def really_convex (𝕜 : Type*) {E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
  [module 𝕜 E] (s : set E) : Prop :=
  s = ∅ ∨ ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s

variables {s : set E}

@[simp]
lemma really_convex_empty : really_convex 𝕜 (∅ : set E) :=
or.inl rfl

@[simp]
lemma really_convex_univ : really_convex 𝕜 (univ : set E) :=
or.inr $ λ w h1w h2w h3w, mem_univ _

-- for every lemma that requires `nontrivial` should we also add a lemma that has the condition
-- `s.nonempty` (or even `nontrivial 𝕜 ∨ s.nonempty`)?
lemma nontrivial.really_convex_iff [nontrivial 𝕜] : really_convex 𝕜 s ↔
  ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s :=
begin
  rw [really_convex, or_iff_right_iff_imp],
  rintro rfl w hw h2w h3w,
  obtain rfl : w = 0,
  { ext, simp [imp_false] at h2w, simp [h2w] },
  simpa using h3w
end

lemma subsingleton.really_convex [subsingleton 𝕜] : really_convex 𝕜 s :=
begin
  rcases eq_empty_or_nonempty s with rfl|⟨z, hz⟩,
  { apply really_convex_empty },
  refine or.inr (λ w hw h2w h3w, _),
  convert hz,
  haveI := module.subsingleton 𝕜 E,
  apply subsingleton.elim
end

lemma really_convex_iff_hull [nontrivial 𝕜] : really_convex 𝕜 s ↔ really_convex_hull 𝕜 s ⊆ s :=
begin
  rw [nontrivial.really_convex_iff],
  split,
  { rintros h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩,
    exact h w w_pos supp_w sum_w },
  { rintros h w w_pos supp_w sum_w,
    exact h ⟨w, w_pos, supp_w, sum_w, rfl⟩ }
end

-- turn this into an iff
lemma really_convex.sum_mem [nontrivial 𝕜] (hs : really_convex 𝕜 s) {ι : Type*} {t : finset ι}
  {w : ι → 𝕜} {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
really_convex_iff_hull.mp hs (sum_mem_really_convex_hull h₀ h₁ hz)

lemma really_convex.finsum_mem [nontrivial 𝕜] (hs : really_convex 𝕜 s) {ι : Type*} {w : ι → 𝕜}
  {z : ι → E} (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i ∈ support w, z i ∈ s) :
  ∑ᶠ i, w i • z i ∈ s :=
begin
  have hw : (support w).finite := support_finite_of_finsum_eq_one h₁,
  have : (support (λ i, w i • z i)).finite := hw.subset (support_smul_subset_left w z),
  rw [finsum_eq_sum_of_support_subset_of_finite _ _ hw],
  swap, { exact support_smul_subset_left w z },
  apply hs.sum_mem (λ i _, h₀ i),
  { rw [← finsum_eq_sum, h₁] },
  { simp_rw [set.finite.mem_to_finset], exact hz },
end

lemma really_convex.add_mem [nontrivial 𝕜] (hs : really_convex 𝕜 s)
  {w₁ w₂ : 𝕜} {z₁ z₂ : E} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) (hz₁ : z₁ ∈ s)
  (hz₂ : z₂ ∈ s) :
  w₁ • z₁ + w₂ • z₂ ∈ s :=
begin
  suffices : ∑ i, @bool.rec (λ _, 𝕜) w₂ w₁ i • (show E, from @bool.rec (λ _, E) z₂ z₁ i) ∈ s,
  { simpa using this },
  apply hs.sum_mem,
  { rintro (_|_) -; assumption },
  { simp [hw] },
  { rintro (_|_) -; assumption },
end

lemma really_convex.inter {t : set E} (hs : really_convex 𝕜 s) (ht : really_convex 𝕜 t) :
  really_convex 𝕜 (s ∩ t) :=
begin
  rcases hs with rfl|hs, { simp },
  rcases ht with rfl|ht, { simp },
  refine or.inr (λ w w_pos supp_w sum_w, _),
  cases set.subset_inter_iff.mp supp_w,
  split,
  { apply hs ; assumption },
  { apply ht ; assumption }
end

lemma really_convex.preimageₛₗ (f : E →ₛₗ[σ.to_ring_hom] E') {s : set E'} (hs : really_convex 𝕜' s) :
  really_convex 𝕜 (f ⁻¹' s) :=
begin
  -- this proof would be easier by casing on `s = ∅`, and
  casesI subsingleton_or_nontrivial 𝕜',
  { haveI : subsingleton E' := module.subsingleton 𝕜' E',
    refine subsingleton.set_cases _ _ s,
    { simp_rw [preimage_empty, really_convex_empty] },
    { simp_rw [preimage_univ, really_convex_univ] } },
  refine or.inr (λ w hw h2w h3w, _),
  have h4w : (support w).finite := support_finite_of_finsum_eq_one h3w,
  have : (support (λ x, w x • x)).finite := h4w.subset (support_smul_subset_left w id),
  simp_rw [mem_preimage, map_finsum f this, map_smulₛₗ f],
  apply hs.finsum_mem,
  { intros i, rw [← map_zero σ], apply σ.monotone', apply hw },
  { rw [← map_finsum _ h4w, h3w, map_one] },
  { intros i hi, apply h2w, rw [mem_support] at hi ⊢, contrapose! hi, rw [hi, map_zero] }
end

lemma really_convex.preimage (f : E →ₗ[𝕜] E₂) {s : set E₂} (hs : really_convex 𝕜 s) :
  really_convex 𝕜 (f ⁻¹' s) :=
really_convex.preimageₛₗ (order_ring_hom.id 𝕜) f hs



/-  The next lemma would also be nice to have.
lemma really_convex_really_convex_hull (s : set E) : really_convex 𝕜 (really_convex_hull 𝕜 s) :=
sorry
 -/


end

section

variables (𝕜 : Type*) {E : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]

lemma really_convex_iff_convex {s : set E} : really_convex 𝕜 s ↔ convex 𝕜 s :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { intros x hx y hy v w hv hw hvw, apply really_convex.add_mem; assumption },
  refine or.inr (λ w hw h2w h3w, h.finsum_mem hw h3w (λi hi, h2w $ mem_support.mpr hi))
end


end
