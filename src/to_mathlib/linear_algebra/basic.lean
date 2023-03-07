import linear_algebra.span


/-! Note: some results should go to `linear_algebra.span`. -/
open submodule function

section
variables {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [semiring R] [semiring R₂]
  [add_comm_monoid M] [add_comm_monoid M₂] {σ₁₂ : R →+* R₂} [module R M]
  [module R₂ M₂]

lemma submodule.sup_eq_span_union (s t : submodule R M) : s ⊔ t = span R (s ∪ t) :=
by rw [span_union, span_eq s, span_eq t]

lemma submodule.sup_eq_top_iff (s t : submodule R M) :
  s ⊔ t = ⊤ ↔ ∀ m : M, ∃ (u ∈ s) (v ∈ t), m = u + v :=
begin
  rw eq_top_iff',
  apply forall_congr (λ m, _),
  rw mem_sup,
  tauto
end

lemma linear_map.eq_on_sup  {s t : submodule R M} {f g : M →ₛₗ[σ₁₂] M₂} (hs : ∀ x ∈ s, f x = g x)
  (ht : ∀ x ∈ t, f x = g x) {x : M} (hx : x ∈ s ⊔ t) : f x = g x :=
linear_map.eq_on_span (show ∀ x ∈ (s : set M) ∪ t, f x = g x, by { rintros x (h|h) ; tauto })
  ((s.sup_eq_span_union t) ▸ hx)

end
section

variables {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [ring R] [ring R₂]
  [add_comm_group M] [add_comm_group M₂] {σ₁₂ : R →+* R₂} [module R M]
  [module R₂ M₂] {p q : submodule R M} [ring_hom_surjective σ₁₂]

lemma submodule.map_inf_le (f : M →ₛₗ[σ₁₂] M₂) (p q : submodule R M) :
  map f (p ⊓ q) ≤ map f p ⊓ map f q :=
set.image_inter_subset _ _ _

lemma submodule.map_inf {f : M →ₛₗ[σ₁₂] M₂} (h : injective f) (p q : submodule R M) :
  map f (p ⊓ q) = map f p ⊓ map f q :=
set_like.coe_injective (set.image_inter h)

lemma linear_map.injective_iff_of_direct_sum (f : M →ₛₗ[σ₁₂] M₂) (hpq : p ⊓ q = ⊥) (hpq' : p ⊔ q = ⊤) :
  injective f ↔ (disjoint p f.ker ∧ disjoint q f.ker ∧ disjoint (map f p) (map f q)) :=
begin
  split,
  { intro h,
    simp [disjoint_iff_inf_le, linear_map.ker_eq_bot.mpr h, ← submodule.map_inf h, hpq] },
  { rintros ⟨hp, hq, h⟩,
    rw linear_map.disjoint_ker at *,
    rw [← linear_map.ker_eq_bot, ← @inf_top_eq _ _ _ f.ker, ← hpq'],
    rw ← le_bot_iff,
    rintros x ⟨hx, hx' : x ∈ p ⊔ q⟩,
    rcases mem_sup.mp hx' with ⟨u, hu, v, hv, rfl⟩,
    rw mem_bot,
    erw [← sub_neg_eq_add, linear_map.sub_mem_ker_iff] at hx,
    have hu' : f u ∈ map f p,
    exact mem_map_of_mem hu,
    have hv' : f (-v) ∈ map f q,
    exact mem_map_of_mem (q.neg_mem hv),
    rw ← hx at hv',
    have H : f u ∈ map f p ⊓ map f q,
    apply mem_inf.mpr ⟨hu', hv'⟩,
    rw [disjoint_iff_inf_le] at h,
    rw [hp u hu (h H), zero_add],
    rw [hp u hu (h H), f.map_zero, f.map_neg, eq_comm, neg_eq_zero] at hx,
    exact hq v hv hx }
end

end


lemma linear_map.ker_inf_eq_bot {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [ring R] [ring R₂]
  [add_comm_group M] [add_comm_group M₂] [module R M] [module R₂ M₂]
  {τ₁₂ : R →+* R₂} {f : M →ₛₗ[τ₁₂] M₂} {S : submodule R M} :
  linear_map.ker f ⊓ S = ⊥ ↔ set.inj_on f S :=
begin
  rw [set.inj_on_iff_injective, inf_comm, ← disjoint_iff, linear_map.disjoint_ker'],
  split,
  { intros h x y hxy,
    exact subtype.coe_injective (h x x.prop y y.prop hxy) },
  { intros h x hx y hy hxy,
    have : (S : set M).restrict f ⟨x, hx⟩ = (S : set M).restrict f ⟨y, hy⟩, from hxy,
    cases h this,
    refl }
end
