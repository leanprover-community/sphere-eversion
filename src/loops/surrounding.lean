import loops.basic
import tactic.fin_cases

/-!
# Surrounding families of loops
-/

open set function finite_dimensional int (hiding range) prod function path
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

lemma loop.surrounds.mono {γ γ' : loop F} {x : F} (h : γ.surrounds x)
  (h2 : range γ ⊆ range γ') : γ'.surrounds x :=
begin
  revert h, simp_rw [loop.surrounds_iff_range_subset_range],
  refine exists_imp_exists (λ t, _),
  refine exists_imp_exists (λ w, _),
  exact and.imp_right (λ h3, subset.trans h3 h2),
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
    { rw trans_range,
      refine union_subset _ hΩ₀.1,
      rwa range_subset_iff },
    rintros t ⟨ht₀, ht₁⟩,
    rw ← range_subset_iff,
    apply trans _ this,
    simp only [γ, loop.round_trip_family, loop.round_trip_range, truncate_range, cast_coe] },
  { rw loop.surrounds_iff_range_subset_range,
    refine ⟨p, w, h, _⟩,
    simp only [γ, loop.round_trip_family_one, loop.round_trip_range, trans_range],
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

protected lemma continuous_b (h : surrounding_family g b γ U) : continuous b :=
by { rw [← show _  = b, from funext (λ x, h.base x 0)],
  exact h.cont.comp (continuous_id.prod_mk
    (continuous_const : continuous (λ _, (0, 0) : _ → ℝ × ℝ))) }

/-- A surrounding family induces a family of paths from `b x` to `b x`.
Currently I(Floris) defined the concatenation we need on `path`, so we need to turn a surrounding
family into the family of paths. -/
@[simps]
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
lemma path_extend_fract (h : surrounding_family g b γ U) (x : E) (t s : ℝ) :
  (h.path x t).extend (fract s) = γ x t s :=
by { rw [extend_extends _ (unit_interval.fract_mem s), ← loop.fract_eq], refl }

@[simp]
lemma range_path (h : surrounding_family g b γ U) (x : E) (t : ℝ) :
  range (h.path x t) = range (γ x t) :=
by simp only [path.coe_mk, surrounding_family.path, range_comp _ coe, subtype.range_coe,
    loop.range_eq_image]

@[simp]
lemma path_t₀ (h : surrounding_family g b γ U) (x : E) :
  h.path x 0 = refl (b x) :=
by { ext t, exact h.t₀ x t }

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
lemma continuous_ρ : continuous ρ :=
continuous_const.max $ continuous_const.min $ continuous_const.mul $ continuous_const.sub
  continuous_id

@[simp] lemma ρ_eq_one_of_le {x : ℝ} (h : x ≤ 1 / 2) : ρ x = 1 :=
begin
  rw [ρ, max_eq_right, min_eq_left],
  { linarith },
  rw [le_min_iff],
  suffices : x ≤ 1, { simpa },
  exact h.trans (by norm_num)
end

@[simp] lemma ρ_eq_one_of_nonpos {x : ℝ} (h : x ≤ 0) : ρ x = 1 :=
ρ_eq_one_of_le $ h.trans (by norm_num)

@[simp] lemma ρ_eq_zero_of_le {x : ℝ} (h : 1 ≤ x) : ρ x = 0 :=
by { rw [ρ, max_eq_left], refine (min_le_right _ _).trans (by linarith) }

@[simp] lemma ρ_eq_one {x : ℝ} : ρ x = 1 ↔ x ≤ 1 / 2 :=
begin
  refine ⟨λ h, _, ρ_eq_one_of_le⟩,
  rw [ρ] at h,
  have := ((max_choice _ _).resolve_left (by norm_num [h])).symm.trans h,
  rw [min_eq_left_iff] at this,
  linarith
end

@[simp] lemma ρ_eq_zero {x : ℝ} : ρ x = 0 ↔ 1 ≤ x :=
begin
  refine ⟨λ h, _, ρ_eq_zero_of_le⟩,
  rw [ρ, max_eq_left_iff, min_le_iff] at h,
  have := h.resolve_left (by norm_num),
  linarith
end

lemma satisfied_or_refund [locally_compact_space E] {γ₀ γ₁ : E → ℝ → loop F}
  (h₀ : surrounding_family g b γ₀ U) (h₁ : surrounding_family g b γ₁ U) :
  ∃ γ : ℝ → E → ℝ → loop F,
    (∀ τ ∈ I, surrounding_family g b (γ τ) U) ∧
    γ 0 = γ₀ ∧
    γ 1 = γ₁ ∧
    continuous ↿γ :=
begin
  let γ : ℝ → E → ℝ → loop F :=
  λ τ x t, loop.of_path $ (h₀.path x $ ρ τ * t).strans (h₁.path x $ ρ (1 - τ) * t)
    (set.proj_Icc 0 1 zero_le_one (1 - τ)),
  have hγ : continuous ↿γ,
  { refine continuous.of_path _ _ _ _ continuous_snd.snd.snd,
    apply continuous.path_strans,
    { refine h₀.cont.comp (continuous_fst.fst.snd.fst.prod_mk (continuous.prod_mk _ _)),
      exact (continuous_ρ.comp continuous_fst.fst.fst).mul continuous_fst.fst.snd.snd.fst,
      exact continuous_subtype_coe.comp continuous_snd },
    { refine h₁.cont.comp (continuous_fst.fst.snd.fst.prod_mk (continuous.prod_mk _ _)),
      refine (continuous_ρ.comp _).mul continuous_fst.fst.snd.snd.fst,
      exact continuous_const.sub continuous_fst.fst.fst,
      exact continuous_subtype_coe.comp continuous_snd },
    { intros x s hs, simp only [proj_Icc_eq_zero, sub_nonpos] at hs,
      simp only [hs, h₀.t₀, zero_mul, surrounding_family.path_apply, ρ_eq_zero_of_le] },
    { intros x s hs, simp only [proj_Icc_eq_one] at hs,
      simp only [hs, h₁.t₀, zero_mul, surrounding_family.path_apply, ρ_eq_zero_of_le] },
    { refine continuous_proj_Icc.comp (continuous_const.sub continuous_fst.fst) },
    { exact continuous_snd } },
  refine ⟨γ, _, _, _, hγ⟩,
  { intros τ hτ, constructor,
    { intros x t, simp only [unit_interval.mk_zero, zero_le_one, extend_extends, path.source,
        loop.of_path_apply, left_mem_Icc, fract_zero] },
    { intros x s, simp [γ] },
    { intros x, cases le_total τ (1 / 2) with h h,
      { have : τ < 1 := h.trans_lt (by norm_num),
        refine (h₀.surrounds x).mono _,
        simp [γ],
        refine subset.trans (by simp [h]) (range_strans_left $ by simp [this]) },
      { have : 0 < τ := lt_of_lt_of_le (by norm_num) h,
        have h : 1 - τ ≤ 1 / 2, { linarith },
        refine (h₁.surrounds x).mono _,
        simp [γ],
        refine subset.trans (by simp [h]) (range_strans_right $ by simp [this]) }, },
    { exact hγ.comp (continuous_const.prod_mk continuous_id) } },
  { ext x t, simp only [one_mul, ρ_eq_one_of_nonpos, surrounding_family.path_extend_fract, sub_zero,
      loop.of_path_apply, unit_interval.mk_one, proj_Icc_right, path.strans_one] },
  { ext x t, simp only [path.strans_zero, unit_interval.mk_zero, one_mul, ρ_eq_one_of_nonpos,
      surrounding_family.path_extend_fract, proj_Icc_left, loop.of_path_apply, sub_self] }
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

-- #print axioms satisfied_or_refund
-- #lint