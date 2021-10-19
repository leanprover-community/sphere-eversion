import loops.basic
import tactic.fin_cases
import to_mathlib.topology.algebra.group
import to_mathlib.topology.constructions

/-!
# Surrounding families of loops
-/

open set function finite_dimensional int (hiding range) prod
open_locale classical topological_space unit_interval

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]

local notation `d` := finrank ℝ F
local notation `smooth_on` := times_cont_diff_on ℝ ⊤

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def loop.surrounds (γ : loop F) (x : F) : Prop :=
  ∃ t w : fin (d + 1) → ℝ, surrounding_pts x (γ ∘ t) w

lemma loop.surrounds_iff_range_subset_range (γ : loop F) (x : F) :
  γ.surrounds x ↔ ∃ (p : fin (d + 1) → F) (w : fin (d + 1) → ℝ),
  surrounding_pts x p w ∧ range p ⊆ range γ :=
begin
  split,
  { exact λ ⟨t, w, h⟩, ⟨(γ ∘ t), w, h, range_comp_subset_range _ _⟩ },
  { rintros ⟨p, w, h₀, h₁⟩,
    rw range_subset_iff at h₁,
    choose t ht using h₁,
    have hpt : γ ∘ t = p := funext ht,
    exact ⟨t, w, hpt.symm ▸ h₀⟩ }
end

lemma surrounding_loop_of_convex_hull {f b : F} {O : set F} (O_op : is_open O) (O_conn : is_connected O)
  (hsf : f ∈ convex_hull ℝ O) (hb : b ∈ O) :
  ∃ γ : ℝ → loop F, continuous_on ↿γ (set.prod I univ) ∧
                    (∀ t, γ t 0 = b) ∧
                    (∀ s, γ 0 s = b) ∧
                    (∀ (t ∈ I) s, γ t s ∈ O) ∧
                    (γ 1).surrounds f :=
begin
  rcases surrounded_of_convex_hull O_op hsf with ⟨p, w, h, hp⟩,
  rw ← O_op.is_connected_iff_is_path_connected at O_conn,
  rcases (O_conn.exists_path_through_family p hp) with ⟨Ω₀, hΩ₀⟩,
  rcases O_conn.joined_in b (p 0) hb (hp 0) with ⟨Ω₁, hΩ₁⟩,
  let γ := loop.round_trip_family (Ω₁.trans Ω₀),
  refine ⟨γ, _, _, _, _, _⟩,
  { exact loop.round_trip_family_continuous.continuous_on },
  { exact loop.round_trip_family_based_at },
  { intro s,
    simp only [γ, loop.round_trip_family_zero],
    refl },
  { have : range (Ω₁.trans Ω₀) ⊆ O,
    { rw path.trans_range,
      refine union_subset _ hΩ₀.1,
      rwa range_subset_iff },
    rintros t ⟨ht₀, ht₁⟩,
    rw ← range_subset_iff,
    apply trans _ this,
    simp only [γ, loop.round_trip_family, loop.round_trip_range, path.truncate_range, path.cast_coe] },
  { rw loop.surrounds_iff_range_subset_range,
    refine ⟨p, w, h, _⟩,
    simp only [γ, loop.round_trip_family_one, loop.round_trip_range, path.trans_range],
    rw range_subset_iff,
    intro i,
    right,
    exact hΩ₀.2 i }
end

/-- `γ` forms a family of loops surrounding `g` with base `b` -/
structure surrounding_family (g b : E → F) (γ : E → ℝ → loop F) (U : set E) : Prop :=
(base : ∀ x t, γ x t 0 = b x)
(t₀ : ∀ x s, γ x 0 s = b x)
(surrounds : ∀ x, (γ x 1).surrounds $ g x)
(cont : continuous ↿γ)

namespace surrounding_family

variables {g b : E → F} {γ : E → ℝ → loop F} {U : set E}

protected lemma one (h : surrounding_family g b γ U) (x : E) (t : ℝ) : γ x t 1 = b x :=
by rw [loop.one, h.base]

/-- A surrounding family induces a family of paths from `b x` to `b x`.
Currently I(Floris) defined the concatenation we need on `path`, so we need to turn a surrounding
family into the family of paths. -/
protected def path (h : surrounding_family g b γ U) (x : E) (t : ℝ) : path (b x) (b x) :=
{ to_fun := λ s, γ x t s,
  continuous_to_fun := begin
    refine continuous.comp _ continuous_subtype_coe,
    refine loop.continuous_of_family _ t,
    refine loop.continuous_of_family_step h.cont x
  end,
  source' := h.base x t,
  target' := h.one x t }

@[simp]
lemma path_extend (h : surrounding_family g b γ U) (x : E) (t s : ℝ) :
  (h.path x t).extend (fract s) = γ x t s :=
sorry

end surrounding_family

/-- `γ` forms a family of loops surrounding `g` with base `b` in `Ω`. -/
structure surrounding_family_in (g b : E → F) (γ : E → ℝ → loop F) (U : set E) (Ω : set $ E × F)
  extends surrounding_family g b γ U : Prop :=
(val_in : ∀ x ∈ U, ∀ (t ∈ I) s, (x, γ x t s) ∈ Ω)

variables {g b : E → F} {Ω : set (E × F)} {U K : set E}


lemma local_loops
  {x₀ : E}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ fst ⁻¹' U))
  (hΩ_conn : ∀ᶠ x in 𝓝 x₀, is_connected (prod.mk x ⁻¹' Ω))
  (hg : ∀ᶠ x in 𝓝 x₀, continuous_at g x) (hb : ∀ᶠ x in 𝓝 x₀, continuous_at b x)
  (hb_in : ∀ᶠ x in 𝓝 x₀, (x, b x) ∈ Ω)
  (hconv : ∀ᶠ x in 𝓝 x₀, g x ∈ convex_hull ℝ (prod.mk x ⁻¹' Ω)) :
∃ (γ : E → ℝ → loop F), (∃ (U ∈ 𝓝 x₀), continuous_on ↿γ (set.prod U $ set.prod I univ)) ∧
  ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) s,
  (x, γ x t s) ∈ Ω ∧
  γ x 0 s = b x ∧
  (γ x 1).surrounds (g x) :=
begin
  have hb_in_x₀ : b x₀ ∈ prod.mk x₀ ⁻¹' Ω := hb_in.self_of_nhds,
  -- let Ωx₀ : set F := connected_component_in (prod.mk x₀ ⁻¹' Ω) ⟨b x₀, hb_in_x₀⟩,
  have hΩ_op_x₀ : is_open (prod.mk x₀ ⁻¹' Ω) := is_open_slice_of_is_open_over hΩ_op,
  -- have hΩx₀_op : is_open Ωx₀ := sorry,
  have hΩ_conn_x₀ : is_connected (prod.mk x₀ ⁻¹' Ω) := hΩ_conn.self_of_nhds,
  rcases surrounding_loop_of_convex_hull hΩ_op_x₀ hΩ_conn_x₀ hconv.self_of_nhds hb_in_x₀ with
    ⟨γ, h1γ, h2γ, h3γ, h4γ, h5γ⟩,
  let δ : E → ℝ → loop F := λ x t, (γ t).shift (b x - b x₀),
  use δ,
  have h1δ : ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) s, (x, δ x t s) ∈ Ω,
  { /-filter_upwards [hΩ_op], intros x hΩx_op t ht s, dsimp only [δ, loop.shift_apply],-/ sorry },
  -- do we need a stronger assumption?
  have h2δ : ∀ᶠ x in 𝓝 x₀, (δ x 1).surrounds (g x),
  { sorry }, -- need lemma 1.7
  split,
  { dsimp only [δ, has_uncurry.uncurry, loop.shift_apply],
    sorry
    /- have h1'γ : continuous_at (↿γ ∘ prod.2) (x, t, s),
    { refine continuous_at.comp _ continuous_at_snd, refine h1γ.continuous_at _, sorry },
    -- this sorry needs a reformulation of either this or surrounding_loop_of_convex_hull
    -- there is a mismatch between the continuous_at here and the continuous_on there
    refine h1'γ.add _,
    refine continuous_at.sub _ continuous_at_const,
    exact continuous_at.comp hbx continuous_at_fst -/ },
  filter_upwards [/-hΩ_op, hΩ_conn, hg, hb_in, hconv,-/ hb, h1δ, h2δ],
  rintro x hbx h1δx h2δx t ht s,
  refine ⟨h1δx t ht s, by simp only [h3γ, loop.shift_apply, add_sub_cancel'_right], h2δx⟩,
end

/-- Function used in `satisfied_or_refund`. Rename. -/
def ρ (t : ℝ) : ℝ := max 0 $ min 1 $ 2 * (1 - t)

@[simp] lemma ρ_zero : ρ 0 = 1 := by norm_num [ρ]
@[simp] lemma ρ_half : ρ 2⁻¹ = 1 := by norm_num [ρ]
@[simp] lemma ρ_one : ρ 1 = 0 := by norm_num [ρ]

-- Should we change the type of `γ` (and `surrounding_family` to user `I` instead of `ℝ` everywhere?
lemma satisfied_or_refund {γ₀ γ₁ : E → ℝ → loop F} (hb : continuous b)
  (h₀ : surrounding_family g b γ₀ U) (h₁ : surrounding_family g b γ₁ U) :
  ∃ γ : ℝ → E → ℝ → loop F,
    (∀ τ ∈ I, surrounding_family g b (γ τ) U) ∧
    γ 0 = γ₀ ∧
    γ 1 = γ₁ ∧
    continuous_on ↿γ (set.prod I $ U.prod $ set.prod I univ) :=
begin
  let γ : ℝ → E → ℝ → loop F :=
  λ τ x t, loop.of_path $ (h₀.path x $ ρ τ * t).trans' (h₁.path x $ ρ (1 - τ) * t)
    (set.proj_Icc 0 1 zero_le_one (1 - τ)),
  refine ⟨γ, _, _, _, _⟩,
  { sorry },
  { ext x t s, sorry; simp only [one_mul, ρ_zero, surrounding_family.path_extend, sub_zero,
      loop.of_path_apply, unit_interval.mk_one, proj_Icc_right, path.trans'_one] },
  { ext x t s, sorry; simp only [path.trans'_zero, unit_interval.mk_zero, one_mul, ρ_zero,
      surrounding_family.path_extend, proj_Icc_left, loop.of_path_apply, sub_self] },
  {
    apply continuous.continuous_on, dsimp [γ],
    refine continuous_uncurry_uncurry.mp _,
    refine continuous_uncurry_uncurry1.mp _,
    refine continuous.of_path _ _ _,
    refine hb.comp continuous_fst.snd,
    have := λ p : (ℝ × E) × ℝ, continuous.trans' (h₀.path p.1.2 $ ρ p.1.1 * p.2),
    -- sorry -- todo: generalize loop.of_path_continuous_family so that base point can vary

    -- rw [← continuous_uncurry_uncurry, ← continuous_uncurry_uncurry],
    -- refine loop.of_path_continuous_family (λ (p : (ℝ × E) × ℝ),

    --        ((h₀.path p.1.2 (ρ p.1.1 * p.2)).trans' (h₁.path p.1.2 (ρ (1 - p.1.1) * p.2))
    --           (proj_Icc 0 1 zero_le_one (1 - p.1.1)))) _, sorry
              }
end

lemma extends_loops {U₀ U₁ K₀ K₁ : set E} (hU₀ : is_open U₀) (hU₁ : is_open U₁)
  (hK₀ : is_compact K₀) (hK₁ : is_compact K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁)
  {γ₀ γ₁ : E → ℝ → loop F}
  (h₀ : surrounding_family g b γ₀ U₀) (h₁ : surrounding_family g b γ₁ U₁) :
  ∃ U ∈ nhds_set (K₀ ∪ K₁), ∃ γ : E → ℝ → loop F,
    surrounding_family g b γ U ∧
    ∀ᶠ x in nhds_set K₀, γ x = γ₀ x :=
sorry


lemma exists_surrounding_loops
  (hU : is_open U) (hK : is_compact K) (hKU : K ⊆ U)
  (hΩ_op : ∀ x ∈ U, is_open (prod.mk x ⁻¹' Ω))
  (hΩ_conn : ∀ x ∈ U, is_connected (prod.mk x ⁻¹' Ω))
  (hg : ∀ x ∈ U, smooth_at g x) (hb : ∀ x ∈ U, smooth_at b x) (hb_in : ∀ x ∈ U, (x, b x) ∈ Ω)
  (hgK : ∀ᶠ x in nhds_set K, g x = b x)
  (hconv : ∀ x ∈ U, g x ∈ convex_hull ℝ (prod.mk x ⁻¹' Ω))
  {γ₀ :  E → ℝ → loop F}
  (hγ₀_surr : ∃ V ∈ nhds_set K, surrounding_family_in g b γ₀ V Ω) :
  ∃ γ : E → ℝ → loop F, (surrounding_family_in g b γ U Ω) ∧
                        (∀ᶠ x in nhds_set K, ∀ (t ∈ I), γ x t = γ₀ x t)  :=
sorry
-- #lint