import linear_algebra.basic

open submodule
variables {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [semiring R] [semiring R₂]
  [add_comm_monoid M] [add_comm_monoid M₂] {σ₁₂ : R →+* R₂} [module R M]
  [module R₂ M₂]

lemma submodule.sup_eq_span_union (s t : submodule R M) : s ⊔ t = span R (s ∪ t) :=
by rw [span_union, span_eq s, span_eq t]

lemma linear_map.eq_on_sup  {s t : submodule R M} {f g : M →ₛₗ[σ₁₂] M₂} (hs : ∀ x ∈ s, f x = g x)
  (ht : ∀ x ∈ t, f x = g x) {x : M} (hx : x ∈ s ⊔ t) : f x = g x :=
linear_map.eq_on_span (show ∀ x ∈ (s : set M) ∪ t, f x = g x, by { rintros x (h|h) ; tauto })
  ((s.sup_eq_span_union t) ▸ hx)
