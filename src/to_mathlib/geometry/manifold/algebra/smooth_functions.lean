import order.filter.germ
import geometry.manifold.algebra.smooth_functions

noncomputable theory

open filter
open_locale manifold topological_space

-- This should be in `order.filter.germ` (and the end of the module docstring of that file
-- should be fixed, it currently refers to things that are in the filter_product file).
instance filter.germ.ordered_comm_ring {α : Type*} (l : filter α) (R : Type*) [ordered_comm_ring R] :
  ordered_comm_ring (germ l R) :=
{ add_le_add_left := begin
    rintros ⟨a⟩ ⟨b⟩ hab ⟨c⟩,
    exact eventually.mono hab (λ x hx, add_le_add_left hx _),
  end,
  zero_le_one :=  eventually_of_forall (λ x, zero_le_one),
  mul_nonneg := begin
    rintros ⟨a⟩ ⟨b⟩ ha hb,
    exact eventually.mono (ha.and hb) (λ x hx, mul_nonneg hx.1 hx.2)
  end,
  ..filter.germ.partial_order,
  ..(by apply_instance : comm_ring (germ l R))}

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{N : Type*} [topological_space N] [charted_space H N]
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{N' : Type*} [topological_space N'] [charted_space H'' N']
(F : Type*) [normed_add_comm_group F] [normed_space 𝕜 F]

section

def cont_mdiff_map.eval (x : N) : C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ →+* 𝕜 :=
{ to_fun := λ f, f x,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

def cont_mdiff_map.max_ideal_at (x : N): ideal (C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯) :=
(cont_mdiff_map.eval I x).ker

local notation `𝔪` := cont_mdiff_map.max_ideal_at

def cont_mdiff_map.residue_field_at (x : N) := C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ ⧸ 𝔪 I x

def cont_mdiff_map.eval_vec (x : N) : C^∞⟮I, N; 𝓘(𝕜, E'), E'⟯ →ₗ[𝕜] E' :=
{ to_fun := λ f, f x,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl }
end


/-- The ideal of smooth functions vanishing near a given point. -/
def cont_mdiff_map.zero_near (x : N) : submodule C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ (C^∞⟮I, N; 𝓘(𝕜, F), F⟯) :=
{ carrier := {f | f =ᶠ[𝓝 x] 0},
  add_mem' := λ f g hf hg, by { rw ← add_zero (0 : N → F), exact hf.add hg },
  zero_mem' := eventually_eq.rfl,
  smul_mem' := λ a f hf, begin
    apply hf.mono,
    intros x hx,
    change (a x) • f x = 0,
    simp only [hx, pi.zero_apply, smul_zero],
  end }

def smooth_germ' (x : N) : subring (germ (𝓝 x) 𝕜) :=
{ carrier := set.range (λ f : C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯, ((f : N → 𝕜) : (germ (𝓝 x) 𝕜))),
  mul_mem' := sorry,
  one_mem' := sorry,
  add_mem' := sorry,
  zero_mem' := sorry,
  neg_mem' := sorry }

instance (x : N) : ordered_comm_ring (smooth_germ' I x) :=
begin
  have := @subring.to_ordered_comm_ring (germ (𝓝 x) 𝕜) _ (smooth_germ' I x),
  sorry
end

def smooth_germ (x : N) := C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ ⧸ (cont_mdiff_map.zero_near I 𝕜 x)

-- Help type class search
instance (x : N) : comm_ring (smooth_germ I x) :=
ideal.quotient.comm_ring (cont_mdiff_map.zero_near I 𝕜 x)

def smooth_germ_vec (x : N) := C^∞⟮I, N; 𝓘(𝕜, F), F⟯ ⧸ (cont_mdiff_map.zero_near I F x)

-- Help type class search
instance (x : N) : add_comm_group (smooth_germ_vec I F x) :=
submodule.quotient.add_comm_group (cont_mdiff_map.zero_near I F x)

def smooth_germ.germ_vec {x : N} : smooth_germ_vec I F x → germ (𝓝 x) F :=
@quotient.map _ _ (submodule.quotient_rel $ cont_mdiff_map.zero_near I F x) (germ_setoid (𝓝 x) F)
cont_mdiff_map.to_fun (λ f g h, eventually_eq_iff_sub.mpr $ (submodule.quotient_rel_r_def _).mp h)

def smooth_germ.germ {x : N} : smooth_germ I x →+* germ (𝓝 x) 𝕜 :=
{ to_fun := smooth_germ.germ_vec I 𝕜,
  map_one' := rfl,
  map_mul' := begin
    sorry
  end,
  map_zero' := rfl,
  map_add' := λ f g, begin

    sorry
  end }


open function

lemma smooth_germ.inj_germ (x : N) : injective (smooth_germ.germ_vec I F : smooth_germ_vec I F x → (𝓝 x).germ F) :=
begin
  letI := germ_setoid (𝓝 x) F,
  rintros ⟨f⟩ ⟨g⟩ h,
  apply quotient.sound,
  exact (submodule.quotient_rel_r_def _).mpr (eventually_eq_iff_sub.mp $ quotient.exact h)
end

instance partial_order_smooth_germ [linear_ordered_field 𝕜] (x : N) : partial_order (smooth_germ I x) :=
partial_order.lift _ (smooth_germ.inj_germ I 𝕜 x)
.
instance [linear_ordered_field 𝕜] (x : N) : ordered_comm_ring (smooth_germ' I x) :=
{ add_le_add_left := begin
  intros a b hab c,
  change smooth_germ.germ I a ≤ smooth_germ.germ I b at hab,
  change smooth_germ.germ I (c+a) ≤ smooth_germ.germ I (c+b),
  rw (smooth_germ.germ I).map_add,
  rw (smooth_germ.germ I).map_add,
  letI := filter.germ.ordered_comm_ring (𝓝 x) 𝕜,
  apply add_le_add_left,
  sorry
end,
  zero_le_one := sorry,
  mul_nonneg := sorry,
  ..partial_order_smooth_germ I x,
  ..ideal.quotient.comm_ring (cont_mdiff_map.zero_near I 𝕜 x)}
#exit


instance (x : N) : module (smooth_germ I x) (smooth_germ_vec I F x) :=
{ smul := quotient.map₂' (λ ρ φ, ρ • φ) /- begin
  intros ρ ρ' hρ φ φ' hφ,
  rw submodule.quotient_rel_r_def at *,
  rw show ρ • φ - ρ' • φ' = ρ • (φ - φ') + (ρ - ρ') • φ', by { rw [smul_sub, sub_smul], abel },
  apply (cont_mdiff_map.zero_near_vec I F x).add_mem,
  apply (cont_mdiff_map.zero_near_vec I F x).smul_mem _ hφ,
  apply eventually.mono hρ,
  intros y hy,
  change ((ρ - ρ') y) • φ' y = 0,
  simp only [hy, pi.zero_apply, zero_smul]
end -/sorry,
  one_smul := begin
    intro φ,
    apply smooth_germ.inj_germ,
    sorry
  end,
  mul_smul := begin

    sorry
  end,
  smul_zero := begin

    sorry
  end,
  smul_add := begin

    sorry
  end,
  add_smul := begin

    sorry
  end,
  zero_smul := begin

    sorry
  end }
instance smooth_pi_has_smul : has_smul C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ (N → F) :=
⟨λ ρ f x, ρ x • f x⟩

instance module_smooth_ger_germ (x : N) : module (smooth_germ I x) (germ (𝓝 x) F) :=
{ smul := quotient.map₂' (λ ρ φ, ρ • φ) sorry,
  one_smul := sorry,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry }
