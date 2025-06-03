import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Hom.Ring

open Function Set

-- TODO: move this lemma and the following one
theorem map_finsum {β α γ : Type*} [AddCommMonoid β] [AddCommMonoid γ]
    {G : Type*} [FunLike G β γ] [AddMonoidHomClass G β γ] (g : G)
    {f : α → β} (hf : (Function.support f).Finite) :
    g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
  (g : β →+ γ).map_finsum hf

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset_of_finite {α M} [CommMonoid M] (f : α → M) {s : Set α}
    (h : mulSupport f ⊆ s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i ∈ hs.toFinset, f i := by
  apply finprod_eq_prod_of_mulSupport_subset f; rwa [Set.Finite.coe_toFinset]

section

variable {𝕜 𝕜' E E₂ E' : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid E₂] [Module 𝕜 E₂] [AddCommMonoid E']
  [Semiring 𝕜'] [PartialOrder 𝕜'] [IsOrderedRing 𝕜'] [Module 𝕜' E'] (σ : 𝕜 →+*o 𝕜')

def reallyConvexHull (𝕜 : Type*) {E : Type*}
    [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    (s : Set E) : Set E :=
  {e | ∃ w : E → 𝕜, 0 ≤ w ∧ support w ⊆ s ∧ ∑ᶠ x, w x = 1 ∧ e = ∑ᶠ x, w x • x}

-- https://xkcd.com/927/
theorem finsum.exists_ne_zero_of_sum_ne_zero {β α : Type*} {s : Finset α} {f : α → β}
    [AddCommMonoid β] : ∑ᶠ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f a ≠ 0 := by
  rw [finsum_mem_finset_eq_sum]
  exact Finset.exists_ne_zero_of_sum_ne_zero

-- rename: `mul_support_finite_of_finprod_ne_one`?
@[to_additive]
theorem finite_of_finprod_ne_one {M : Type*} {ι : Sort _} [CommMonoid M] {f : ι → M}
    (h : ∏ᶠ i, f i ≠ 1) : (mulSupport f).Finite := by
  classical
  rw [finprod_def] at h
  contrapose h
  rw [Classical.not_not, dif_neg h]

theorem support_finite_of_finsum_eq_of_neZero {M : Type*} {ι : Sort _} [AddCommMonoid M]
    {f : ι → M} {x : M} [NeZero x] (h : ∑ᶠ i, f i = x) : (support f).Finite := by
  apply finite_of_finsum_ne_zero
  rw [h]
  apply NeZero.ne

@[to_additive]
theorem Subsingleton.mulSupport_eq {α β} [Subsingleton β] [One β] (f : α → β) :
    mulSupport f = ∅ := by
  rw [mulSupport_eq_empty_iff]; apply Subsingleton.elim

theorem support_finite_of_finsum_eq_one {M : Type*} {ι : Sort _} [NonAssocSemiring M] {f : ι → M}
    (h : ∑ᶠ i, f i = 1) : (support f).Finite := by
  cases subsingleton_or_nontrivial M
  · simp_rw [Subsingleton.support_eq, finite_empty]
  exact support_finite_of_finsum_eq_of_neZero h

theorem finsum_sum_filter {α β M : Type*} [AddCommMonoid M] (f : β → α) (s : Finset β)
    [DecidableEq α] (g : β → M) :
    ∑ᶠ x : α, ∑ y ∈ Finset.filter (fun j : β ↦ f j = x) s, g y = ∑ k ∈ s, g k := by
  rw [finsum_eq_finset_sum_of_support_subset]
  · rw [Finset.sum_image']
    exact fun _ _ ↦ rfl
  · intro x hx
    rw [mem_support] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    simp at h ⊢
    exact ⟨a, h⟩

theorem sum_mem_reallyConvexHull {s : Set E} {ι : Type*} {t : Finset ι} {w : ι → 𝕜} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ reallyConvexHull 𝕜 s := by
  classical
  refine ⟨fun e ↦ ∑ᶠ i ∈ t.filter fun j ↦ z j = e, w i, ?_, ?_, ?_, ?_⟩
  · rw [Pi.le_def]
    exact fun e ↦ finsum_nonneg fun i ↦ finsum_nonneg fun hi ↦ h₀ _ (Finset.mem_of_mem_filter i hi)
  · intro e he
    rw [mem_support] at he
    obtain ⟨a, h, ha⟩ := finsum.exists_ne_zero_of_sum_ne_zero he
    rw [Finset.mem_filter] at h
    rcases h with ⟨h, rfl⟩
    exact hz a h
  · simp_rw [← h₁, finsum_mem_finset_eq_sum, finsum_sum_filter z ..]
  · simp_rw [finsum_mem_finset_eq_sum, Finset.sum_smul]
    rw [← finsum_sum_filter z]
    congr with x
    rw [Finset.sum_congr rfl]
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]

theorem reallyConvexHull_mono : Monotone (reallyConvexHull 𝕜 : Set E → Set E) := by
  rintro s t h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩
  exact ⟨w, w_pos, supp_w.trans h, sum_w, rfl⟩

/-- Generalization of `Convex` to semirings. We only add the `s = ∅` clause if `𝕜` is trivial. -/
def ReallyConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    (s : Set E) : Prop :=
  s = ∅ ∨ ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s

variable {s : Set E}

@[simp]
theorem reallyConvex_empty : ReallyConvex 𝕜 (∅ : Set E) := Or.inl rfl

@[simp]
theorem reallyConvex_univ : ReallyConvex 𝕜 (univ : Set E) := Or.inr fun _ _ _ _ ↦ mem_univ _

-- for every lemma that requires `Nontrivial` should we also add a lemma that has the condition
-- `s.Nonempty` (or even `Nontrivial 𝕜 ∨ s.Nonempty`)?
theorem Nontrivial.reallyConvex_iff [Nontrivial 𝕜] :
    ReallyConvex 𝕜 s ↔ ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s := by
  rw [ReallyConvex, or_iff_right_iff_imp]
  rintro rfl w hw h2w h3w
  obtain rfl : w = 0 := by ext; simp [imp_false] at h2w; simp [h2w]
  simp at h3w

theorem Subsingleton.reallyConvex [Subsingleton 𝕜] : ReallyConvex 𝕜 s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨z, hz⟩)
  · exact reallyConvex_empty
  · refine Or.inr fun w _ _ _ ↦ ?_
    convert hz
    haveI := Module.subsingleton 𝕜 E
    exact Subsingleton.elim ..

theorem reallyConvex_iff_hull [Nontrivial 𝕜] : ReallyConvex 𝕜 s ↔ reallyConvexHull 𝕜 s ⊆ s := by
  rw [Nontrivial.reallyConvex_iff]
  constructor
  · rintro h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩
    exact h w w_pos supp_w sum_w
  · rintro h w w_pos supp_w sum_w
    exact h ⟨w, w_pos, supp_w, sum_w, rfl⟩

-- turn this into an iff
theorem ReallyConvex.sum_mem [Nontrivial 𝕜] (hs : ReallyConvex 𝕜 s) {ι : Type*} {t : Finset ι}
    {w : ι → 𝕜} {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : ∑ i ∈ t, w i • z i ∈ s :=
  reallyConvex_iff_hull.mp hs (sum_mem_reallyConvexHull h₀ h₁ hz)

theorem ReallyConvex.finsum_mem [Nontrivial 𝕜] (hs : ReallyConvex 𝕜 s) {ι : Type*} {w : ι → 𝕜}
    {z : ι → E} (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i ∈ support w, z i ∈ s) :
    ∑ᶠ i, w i • z i ∈ s := by
  rw [finsum_eq_sum_of_support_subset_of_finite _ _ (support_finite_of_finsum_eq_one h₁)]
  swap; · exact support_smul_subset_left w z
  apply hs.sum_mem fun i _ ↦ h₀ i
  · rw [← finsum_eq_sum, h₁]
  · simp_rw [Set.Finite.mem_toFinset]; exact hz

theorem ReallyConvex.add_mem (hs : ReallyConvex 𝕜 s) {w₁ w₂ : 𝕜} {z₁ z₂ : E}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) (hz₁ : z₁ ∈ s) (hz₂ : z₂ ∈ s) :
    w₁ • z₁ + w₂ • z₂ ∈ s := by
  cases subsingleton_or_nontrivial 𝕜
  · have := Module.subsingleton 𝕜 E
    rwa [Subsingleton.mem_iff_nonempty] at hz₁ ⊢
  suffices ∑ b : Bool, cond b w₁ w₂ • cond b z₁ z₂ ∈ s by simpa using this
  apply hs.sum_mem <;> simp [*]

theorem ReallyConvex.inter {t : Set E} (hs : ReallyConvex 𝕜 s) (ht : ReallyConvex 𝕜 t) :
    ReallyConvex 𝕜 (s ∩ t) := by
  rcases hs with (rfl | hs); · simp
  rcases ht with (rfl | ht); · simp
  refine Or.inr fun w w_pos supp_w sum_w ↦ ?_
  cases Set.subset_inter_iff.mp supp_w
  constructor
  · apply hs <;> assumption
  · apply ht <;> assumption

theorem ReallyConvex.preimageₛₗ (f : E →ₛₗ[σ.toRingHom] E') {s : Set E'} (hs : ReallyConvex 𝕜' s) :
    ReallyConvex 𝕜 (f ⁻¹' s) := by
  -- this proof would be easier by casing on `s = ∅`, and
  cases subsingleton_or_nontrivial 𝕜'
  · haveI : Subsingleton E' := Module.subsingleton 𝕜' E'
    refine Subsingleton.set_cases ?_ ?_ s
    · simp_rw [preimage_empty, reallyConvex_empty]
    · simp_rw [preimage_univ, reallyConvex_univ]
  · refine Or.inr fun w hw h2w h3w ↦ ?_
    have h4w : (support w).Finite := support_finite_of_finsum_eq_one h3w
    have : (support fun x ↦ w x • x).Finite := h4w.subset (support_smul_subset_left w id)
    simp_rw [mem_preimage, map_finsum f this, map_smulₛₗ f]
    apply hs.finsum_mem
    · intro i; rw [← map_zero σ]; apply σ.monotone'; apply hw
    · rw [← map_finsum _ h4w, h3w, map_one]
    · intro i hi; apply h2w; rw [mem_support] at hi ⊢; contrapose! hi; rw [hi, map_zero]

theorem ReallyConvex.preimage (f : E →ₗ[𝕜] E₂) {s : Set E₂} (hs : ReallyConvex 𝕜 s) :
    ReallyConvex 𝕜 (f ⁻¹' s) :=
  ReallyConvex.preimageₛₗ (OrderRingHom.id 𝕜) f hs

/-  The next lemma would also be nice to have.
lemma reallyConvex_reallyConvexHull (s : Set E) : reallyConvex 𝕜 (reallyConvexHull 𝕜 s) := sorry
 -/
end

section

variable (𝕜 : Type*) {E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

theorem reallyConvex_iff_convex {s : Set E} : ReallyConvex 𝕜 s ↔ Convex 𝕜 s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro x hx y hy v w hv hw hvw; apply ReallyConvex.add_mem <;> assumption
  · exact Or.inr fun w hw h2w h3w ↦ h.finsum_mem hw h3w fun i hi ↦ h2w <| mem_support.mpr hi

end
