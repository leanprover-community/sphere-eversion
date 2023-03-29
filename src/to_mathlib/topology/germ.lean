import order.filter.germ
import topology.constructions

import to_mathlib.topology.nhds_set

open_locale topology
open filter

/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def filter.germ.value {X α : Type*} [topological_space X] {x : X} (φ : germ (𝓝 x) α) : α :=
quotient.lift_on' φ (λ f, f x) (λ f g h, by { dsimp only, rw eventually.self_of_nhds h })

/-- Given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and `A : set X`,
build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A x f) ↔ ∀ᶠ x near A, P x f`, see
`forall_restrict_germ_predicate_iff` for this equivalence. -/
def restrict_germ_predicate {X Y : Type*} [topological_space X]
  (P : Π x : X, germ (𝓝 x) Y → Prop) (A : set X) : Π x : X, germ (𝓝 x) Y → Prop :=
λ x φ, quotient.lift_on' φ (λ f, x ∈ A → ∀ᶠ y in 𝓝 x, P y f) begin
  have : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f',
  { intros f f' hff' hf,
    apply (hf.and $ eventually.eventually_nhds hff').mono,
    rintros y ⟨hy, hy'⟩,
    rwa germ.coe_eq.mpr (eventually_eq.symm hy') },
  exact λ f f' hff', propext $ forall_congr $ λ _, ⟨this f f' hff', this f' f hff'.symm⟩,
end

lemma filter.eventually.germ_congr {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f g : X → Y}
  (hf : ∀ᶠ x in 𝓝ˢ A, P x f) (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) : ∀ᶠ x in 𝓝ˢ A, P x g :=
begin
  rw eventually_nhds_set_iff at *,
  intros x hx,
  apply ((hf x hx).and (h x hx).eventually_nhds).mono,
  intros y hy,
  convert hy.1 using 1,
  apply quotient.sound,
  exact hy.2
end


lemma restrict_germ_predicate_congr {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f g : X → Y} {x : X}
  (hf : restrict_germ_predicate P A x f) (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) :
  restrict_germ_predicate P A x g :=
begin
  intros hx,
  apply ((hf hx).and $ eventually_nhds_set_iff.mp h x hx).eventually_nhds.mono,
  intros y hy,
  rw eventually_and at hy,
  convert hy.1.self_of_nhds using 1,
  apply quotient.sound,
  exact hy.2,
end


lemma forall_restrict_germ_predicate_iff {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} :
  (∀ x, restrict_germ_predicate P A x f) ↔ ∀ᶠ x in 𝓝ˢ A, P x f :=
by { rw eventually_nhds_set_iff, exact iff.rfl }

lemma  forall_restrict_germ_predicate_of_forall {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} (h : ∀ x, P x f) :
  ∀ x, restrict_germ_predicate P A x f :=
forall_restrict_germ_predicate_iff.mpr (eventually_of_forall h)

lemma filter.eventually_eq.comp_fun {α β γ : Type*} {f g : β → γ} {l : filter α} {l' : filter β}
  (h : f =ᶠ[l'] g) {φ : α → β} (hφ : tendsto φ l l') : f ∘ φ =ᶠ[l] g ∘ φ :=
hφ h

def filter.germ.slice_left {X Y Z : Type*} [topological_space X] [topological_space Y] {p : X × Y}
  (P : germ (𝓝 p) Z) : germ (𝓝 p.1) Z :=
P.lift_on (λ f, ((λ x', f (x', p.2)) : germ (𝓝 p.1) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 p.1).germ_setoid Z) _ _
     (hfg.comp_fun begin
       rw ← (prod.mk.eta : (p.1, p.2) = p),
       exact (continuous.prod.mk_left p.2).continuous_at,
     end))

def filter.germ.slice_right {X Y Z : Type*} [topological_space X] [topological_space Y] {p : X × Y}
  (P : germ (𝓝 p) Z) : germ (𝓝 p.2) Z :=
P.lift_on (λ f, ((λ y, f (p.1, y)) : germ (𝓝 p.2) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 p.2).germ_setoid Z) _ _
     (hfg.comp_fun begin
       rw ← (prod.mk.eta : (p.1, p.2) = p),
       exact (continuous.prod.mk p.1).continuous_at,
     end))
