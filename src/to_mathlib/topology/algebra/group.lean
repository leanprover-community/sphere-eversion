import topology.algebra.group_with_zero
import topology.algebra.group

variables {α X : Type*} [topological_space X]
variables {G : Type*} [topological_space G] [group G] [topological_group G]

open filter
open_locale topological_space

/-! multiplicative names here have primess because of the conflicting names with `group_with_zero`
names -/

@[to_additive]
lemma continuous_at.inv {f : X → G} {x : X} (hf : continuous_at f x) :
  continuous_at (λ x, (f x)⁻¹) x :=
continuous_at_inv.comp hf

@[to_additive]
lemma continuous_div : continuous (λ p : G × G, p.1 / p.2) :=
by { simp only [div_eq_mul_inv],
  exact (@continuous_mul G _ _ _).comp (continuous_id.prod_map continuous_inv), }

@[continuity, to_additive continuous.sub'] -- name clash
lemma continuous.div' {f g : X → G} (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x / g x) :=
continuous_div.comp (hf.prod_mk hg : _)

-- should `to_additive` be doing this?
attribute [continuity] continuous.sub

@[to_additive continuous_sub_left]
lemma continuous_div_left' (a : G) : continuous (λ b : G, a / b) :=
continuous_const.div' continuous_id

@[to_additive continuous_sub_right]
lemma continuous_div_right' (a : G) : continuous (λ b : G, b / a) :=
continuous_id.div' continuous_const

@[to_additive continuous_on.sub'] -- name clash
lemma continuous_on.div' {f g : X → G} {s : set X} (hf : continuous_on f s)
  (hg : continuous_on g s) :
  continuous_on (λ x, f x / g x) s :=
(continuous_div.comp_continuous_on (hf.prod hg) : _)

@[to_additive tendsto_sub]
lemma tendsto_div' {a b : G} : tendsto (λ p : G × G, p.fst / p.snd) (𝓝 (a, b)) (𝓝 (a / b)) :=
continuous_iff_continuous_at.mp continuous_div (a, b)

@[to_additive] -- name clash
lemma filter.tendsto.div' {f g : α → G} {x : filter α} {a b : G}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x / g x) x (𝓝 (a / b)) :=
tendsto_div'.comp (hf.prod_mk_nhds hg)

@[to_additive filter.tendsto.const_sub]
lemma filter.tendsto.const_div' (b : G) {c : G} {f : α → G} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ k : α, b / f k) l (𝓝 (b / c)) :=
tendsto_const_nhds.div' h

@[to_additive filter.tendsto.sub_const]
lemma filter.tendsto.div_const' (b : G) {c : G} {f : α → G} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ k : α, f k / b) l (𝓝 (c / b)) :=
h.div' tendsto_const_nhds

@[to_additive continuous_at.sub]
lemma continuous_at.div' {f g : X → G} {x : X} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x / g x) x :=
hf.div' hg

@[to_additive continuous_within_at.sub]
lemma continuous_within_at.div' {f g : X → G} {s : set X} {x : X} (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x / g x) s x :=
hf.div' hg