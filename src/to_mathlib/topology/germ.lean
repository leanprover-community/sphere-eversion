import order.filter.germ
import topology.constructions

import topology.connected
import topology.separation

import to_mathlib.topology.nhds_set

open_locale topology
open filter set

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

def filter.germ.is_constant {X Y : Type*} [topological_space X] {x} (P : germ (𝓝 x) Y) : Prop :=
P.lift_on (λ f, ∀ᶠ x' in 𝓝 x, f x' = f x) begin
  suffices : ∀ (f g : X → Y), f =ᶠ[𝓝 x] g →
     (∀ᶠ x' in 𝓝 x, f x' = f x) → ∀ᶠ x' in 𝓝 x, g x' = g x,
  from λ f g hfg, propext ⟨λ h, this f g hfg h, λ h, this g f hfg.symm h⟩,
  rintros f g hfg hf,
  apply (hf.and hfg).mono (λ x' hx', _),
  rw [← hx'.2, hx'.1, hfg.eq_of_nhds],
end

lemma eq_of_germ_is_constant {X Y : Type*} [topological_space X] [preconnected_space X]
  {f : X → Y} (h : ∀ x : X, (f : germ (𝓝 x) Y).is_constant) (x x' : X) : f x = f x' :=
begin
  revert x,
  erw ← eq_univ_iff_forall,
  apply is_clopen.eq_univ _ (⟨x', rfl⟩ : {x | f x = f x'}.nonempty),
  refine ⟨is_open_iff_eventually.mpr (λ x hx, hx ▸ h x), _⟩,
  rw is_closed_iff_frequently,
  rintros x hx,
  rcases (eventually.and_frequently (h x) hx).exists with ⟨x'', H⟩,
  exact H.1.symm.trans H.2
end

lemma eq_of_germ_is_constant_on {X Y : Type*} [topological_space X]
  {f : X → Y} {s : set X} (h : ∀ x ∈ s, (f : germ (𝓝 x) Y).is_constant)
  (hs : is_preconnected s) {x x' : X} (x_in : x ∈ s) (x'_in : x' ∈ s) : f x = f x' :=
begin
  haveI := is_preconnected_iff_preconnected_space.mp hs,
  let F : s → Y := f ∘ coe,
  change F ⟨x, x_in⟩ = F ⟨x', x'_in⟩,
  apply eq_of_germ_is_constant,
  rintros ⟨x, hx⟩,
  have : continuous_at (coe : s → X) ⟨x, hx⟩,
  exact continuous_at_subtype_coe,
  exact this (h x hx)
end
