import Mathlib.LinearAlgebra.Span

/-! Note: some results should go to `linear_algebra.span`. -/


open Submodule Function

section

variable {R : Type _} {R₂ : Type _} {M : Type _} {M₂ : Type _} [Semiring R] [Semiring R₂]
  [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R →+* R₂} [Module R M] [Module R₂ M₂]

theorem Submodule.sup_eq_span_union (s t : Submodule R M) : s ⊔ t = span R (s ∪ t) := by
  rw [span_union, span_eq s, span_eq t]

theorem Submodule.sup_eq_top_iff (s t : Submodule R M) :
    s ⊔ t = ⊤ ↔ ∀ m : M, ∃ u ∈ s, ∃ v ∈ t, m = u + v := by
  rw [eq_top_iff']
  refine forall_congr' fun m => ?_
  rw [mem_sup]
  tauto

theorem LinearMap.eq_on_sup {s t : Submodule R M} {f g : M →ₛₗ[σ₁₂] M₂} (hs : ∀ x ∈ s, f x = g x)
    (ht : ∀ x ∈ t, f x = g x) {x : M} (hx : x ∈ s ⊔ t) : f x = g x :=
  LinearMap.eqOn_span (show ∀ x ∈ (s : Set M) ∪ t, f x = g x by rintro x (h | h) <;> tauto)
    (s.sup_eq_span_union t ▸ hx)

end

section

variable {R : Type _} {R₂ : Type _} {M : Type _} {M₂ : Type _} [Ring R] [Ring R₂] [AddCommGroup M]
  [AddCommGroup M₂] {σ₁₂ : R →+* R₂} [Module R M] [Module R₂ M₂] {p q : Submodule R M}
  [RingHomSurjective σ₁₂]

theorem Submodule.map_inf_le (f : M →ₛₗ[σ₁₂] M₂) (p q : Submodule R M) :
    map f (p ⊓ q) ≤ map f p ⊓ map f q :=
  Set.image_inter_subset _ _ _

theorem Submodule.map_inf {f : M →ₛₗ[σ₁₂] M₂} (h : Injective f) (p q : Submodule R M) :
    map f (p ⊓ q) = map f p ⊓ map f q :=
  SetLike.coe_injective (Set.image_inter h)

theorem LinearMap.injective_iff_of_direct_sum (f : M →ₛₗ[σ₁₂] M₂) (hpq : p ⊓ q = ⊥)
    (hpq' : p ⊔ q = ⊤) :
    Injective f ↔ Disjoint p (LinearMap.ker f) ∧ Disjoint q (LinearMap.ker f) ∧
      Disjoint (map f p) (map f q) := by
  constructor
  · intro h
    simp [disjoint_iff_inf_le, LinearMap.ker_eq_bot.mpr h, ← Submodule.map_inf h, hpq]
  · rintro ⟨hp, hq, h⟩
    rw [LinearMap.disjoint_ker] at *
    rw [← LinearMap.ker_eq_bot, ← @inf_top_eq _ _ _ (LinearMap.ker f), ← hpq']
    rw [← le_bot_iff]
    rintro x ⟨hx, hx' : x ∈ p ⊔ q⟩
    rcases mem_sup.mp hx' with ⟨u, hu, v, hv, rfl⟩
    rw [mem_bot]
    erw [← sub_neg_eq_add, LinearMap.sub_mem_ker_iff] at hx 
    have hu' : f u ∈ map f p := mem_map_of_mem hu
    have hv' : f (-v) ∈ map f q := mem_map_of_mem (q.neg_mem hv)
    rw [← hx] at hv' 
    have H : f u ∈ map f p ⊓ map f q
    apply mem_inf.mpr ⟨hu', hv'⟩
    rw [disjoint_iff_inf_le] at h 
    rw [hp u hu (h H), zero_add]
    rw [hp u hu (h H), f.map_zero, f.map_neg, eq_comm, neg_eq_zero] at hx 
    exact hq v hv hx

end

theorem LinearMap.ker_inf_eq_bot {R : Type _} {R₂ : Type _} {M : Type _} {M₂ : Type _} [Ring R]
    [Ring R₂] [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} : LinearMap.ker f ⊓ S = ⊥ ↔ Set.InjOn f S := by
  rw [Set.injOn_iff_injective, inf_comm, ← disjoint_iff, LinearMap.disjoint_ker']
  constructor
  · intro h x y hxy
    exact Subtype.coe_injective (h x x.prop y y.prop hxy)
  · intro h x hx y hy hxy
    have : (S : Set M).restrict f ⟨x, hx⟩ = (S : Set M).restrict f ⟨y, hy⟩ := hxy
    cases h this
    rfl

