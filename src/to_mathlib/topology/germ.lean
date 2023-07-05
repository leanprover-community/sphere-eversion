import order.filter.germ
import topology.algebra.ring
import analysis.calculus.fderiv
import algebra.order.hom.ring

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]

open_locale topological_space
open filter set

namespace filter.germ
/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [topological_space X] {x : X} (φ : germ (𝓝 x) α) : α :=
quotient.lift_on' φ (λ f, f x) (λ f g h, by { dsimp only, rw eventually.self_of_nhds h })

lemma value_smul {X α β : Type*} [topological_space X] {x : X} [has_smul α β]
  (φ : germ (𝓝 x) α) (ψ : germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl))

@[to_additive]
def value_mul_hom {X E : Type*} [monoid E] [topological_space X] {x : X} :
  germ (𝓝 x) E →* E :=
{ to_fun := filter.germ.value,
  map_one' := rfl,
  map_mul' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl)) }

def valueₗ {X 𝕜 E : Type*} [semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space X] {x : X} : germ (𝓝 x) E →ₗ[𝕜] E :=
{ map_smul' := λ r φ, germ.induction_on φ (λ f, rfl),
  .. filter.germ.value_add_hom }

def value_ring_hom {X E : Type*} [semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+* E :=
{ ..filter.germ.value_mul_hom,
  ..filter.germ.value_add_hom }

def value_order_ring_hom {X E : Type*} [ordered_semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+*o E :=
{ monotone' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g h, h.self_of_nhds)),
  ..filter.germ.value_ring_hom }

def _root_.subring.ordered_subtype {R} [ordered_ring R] (s : subring R) : s →+*o R :=
{ monotone' := λ x y h, h,
  ..s.subtype }

end filter.germ
