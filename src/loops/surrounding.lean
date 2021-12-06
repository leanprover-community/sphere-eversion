import loops.basic
import tactic.fin_cases
import topology.metric_space.emetric_paracompact

/-!
# Surrounding families of loops
-/

open set function finite_dimensional int prod function path filter
open_locale classical topological_space unit_interval

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

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

lemma surrounding_loop_of_convex_hull [finite_dimensional ℝ F] {f b : F} {O : set F}
  (O_op : is_open O) (O_conn : is_connected O)
  (hsf : f ∈ convex_hull ℝ O) (hb : b ∈ O) :
  ∃ γ : ℝ → loop F, continuous ↿γ ∧
                    (∀ t, γ t 0 = b) ∧
                    (∀ s, γ 0 s = b) ∧
                    (∀ t s, γ t s ∈ O) ∧
                    (γ 1).surrounds f :=
begin
  rcases surrounded_of_convex_hull O_op hsf with ⟨p, w, h, hp⟩,
  rw ← O_op.is_connected_iff_is_path_connected at O_conn,
  rcases (O_conn.exists_path_through_family p hp) with ⟨Ω₀, hΩ₀⟩,
  rcases O_conn.joined_in b (p 0) hb (hp 0) with ⟨Ω₁, hΩ₁⟩,
  let γ := loop.round_trip_family (Ω₁.trans Ω₀),
  refine ⟨γ, _, _, _, _, _⟩,
  { exact loop.round_trip_family_continuous },
  { exact loop.round_trip_family_based_at },
  { intro s,
    simp only [γ, loop.round_trip_family_zero],
    refl },
  { have : range (Ω₁.trans Ω₀) ⊆ O,
    { rw trans_range,
      refine union_subset _ hΩ₀.1,
      rwa range_subset_iff },
    rintros t,
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

/-- `γ` forms a family of loops surrounding `g` with base `b`.
In contrast to the notes we assume that `base` and `t₀` hold universally. -/
structure surrounding_family (g b : E → F) (γ : E → ℝ → loop F) (U : set E) : Prop :=
(base : ∀ (x : E) (t : ℝ), γ x t 0 = b x)
(t₀ : ∀ (x : E) (s : ℝ), γ x 0 s = b x)
(surrounds : ∀ x ∈ U, (γ x 1).surrounds $ g x)
(cont : continuous ↿γ)

/-- `γ` forms a family of loops surrounding `g` with base `b` in `Ω`. -/
structure surrounding_family_in (g b : E → F) (γ : E → ℝ → loop F) (U : set E) (Ω : set $ E × F)
  extends surrounding_family g b γ U : Prop :=
(val_in' : ∀ (x ∈ U) (t ∈ I) (s ∈ I), (x, γ x t s) ∈ Ω)

namespace surrounding_family

variables {g b : E → F} {γ : E → ℝ → loop F} {U : set E}

protected lemma one (h : surrounding_family g b γ U) (x : E) (t : ℝ) : γ x t 1 = b x :=
by rw [loop.one, h.base]

protected lemma continuous_b (h : surrounding_family g b γ U) : continuous b :=
by { refine continuous.congr _ (λ x, h.base x 0),
     exact h.cont.comp (continuous_id.prod_mk
      (continuous_const : continuous (λ _, ((0, 0) : ℝ × ℝ)))) }

protected lemma change_set (h : surrounding_family g b γ U) {V : set E}
  (hV : ∀ x ∈ V \ U, (γ x 1).surrounds $ g x) :
  surrounding_family g b γ V :=
begin
  refine ⟨h.base, h.t₀, λ x hx, _, h.cont⟩,
  by_cases h2x : x ∈ U, exact h.surrounds x h2x, exact hV x ⟨hx, h2x⟩
end

protected lemma mono (h : surrounding_family g b γ U) {V : set E} (hVU : V ⊆ U) :
  surrounding_family g b γ V :=
⟨h.base, h.t₀, λ x hx, h.surrounds x (hVU hx), h.cont⟩

/-- A surrounding family induces a family of paths from `b x` to `b x`.
Currently I(Floris) defined the concatenation we need on `path`, so we need to turn a surrounding
family into the family of paths. -/
@[simps]
protected def path (h : surrounding_family g b γ U) (x : E) (t : ℝ) :
  path (b x) (b x) :=
{ to_fun := λ s, γ x t s,
  continuous_to_fun := begin
    refine continuous.comp _ continuous_subtype_coe,
    refine loop.continuous_of_family _ t,
    refine loop.continuous_of_family_step h.cont x
  end,
  source' := h.base x t,
  target' := h.one x t }

lemma continuous_path {X : Type*} [topological_space X] (h : surrounding_family g b γ U)
  {t : X → ℝ} {f : X → E} {s : X → I} (hf : continuous f) (ht : continuous t)
  (hs : continuous s) : continuous (λ x, h.path (f x) (t x) (s x)) :=
h.cont.comp (hf.prod_mk $ ht.prod_mk hs.subtype_coe)

@[simp]
lemma path_extend_fract (h : surrounding_family g b γ U) (t s : ℝ) (x : E) :
  (h.path x t).extend (fract s) = γ x t s :=
by { rw [extend_extends _ (unit_interval.fract_mem s), ← loop.fract_eq], refl }

@[simp]
lemma range_path (h : surrounding_family g b γ U) (x : E) (t : ℝ) :
  range (h.path x t) = range (γ x t) :=
by simp only [path.coe_mk, surrounding_family.path, range_comp _ coe, subtype.range_coe,
    loop.range_eq_image]

@[simp]
lemma path_t₀ (h : surrounding_family g b γ U) (x : E) : h.path x 0 = refl (b x) :=
by { ext t, exact h.t₀ x t }

end surrounding_family

variables {g b : E → F} {γ : E → ℝ → loop F} {U K : set E} {Ω : set (E × F)}

namespace surrounding_family_in

/-- Abbreviation for `to_surrounding_family` -/
abbreviation to_sf (h : surrounding_family_in g b γ U Ω) : surrounding_family g b γ U :=
h.to_surrounding_family

lemma val_in (h : surrounding_family_in g b γ U Ω) {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ I)
  {s : ℝ} : (x, γ x t s) ∈ Ω :=
by { rw [← loop.fract_eq], exact h.val_in' x hx t ht (fract s) (unit_interval.fract_mem s) }

protected lemma mono (h : surrounding_family_in g b γ U Ω) {V : set E} (hVU : V ⊆ U) :
  surrounding_family_in g b γ V Ω :=
⟨h.to_sf.mono hVU, λ x hx, h.val_in' x (hVU hx)⟩

end surrounding_family_in

/--
Note: The conditions in this lemma are currently a bit weaker than the ones mentioned in the
blueprint.

It would be nice if we work with `def`s and lemmas instead of these existential statements.
-/
lemma local_loops [finite_dimensional ℝ F]
  {x₀ : E}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ fst ⁻¹' U))
  (hΩ_conn : is_connected (prod.mk x₀ ⁻¹' Ω))
  (hg : continuous_at g x₀) (hb : continuous b)
  (hb_in : (x₀, b x₀) ∈ Ω)
  (hconv : g x₀ ∈ convex_hull ℝ (prod.mk x₀ ⁻¹' Ω)) :
  ∃ (γ : E → ℝ → loop F) (U ∈ 𝓝 x₀), surrounding_family_in g b γ U Ω :=
begin
  have hbx₀ : continuous_at b x₀ := hb.continuous_at,
  have hΩ_op_x₀ : is_open (prod.mk x₀ ⁻¹' Ω) := is_open_slice_of_is_open_over hΩ_op,
  rcases surrounding_loop_of_convex_hull hΩ_op_x₀ hΩ_conn hconv hb_in with
    ⟨γ, h1γ, h2γ, h3γ, h4γ, h5γ⟩,
  let δ : E → ℝ → loop F := λ x t, (γ t).shift (b x - b x₀),
  have hδ : continuous ↿δ,
  { dsimp only [δ, has_uncurry.uncurry, loop.shift_apply],
    refine (h1γ.comp continuous_snd).add _,
    refine continuous.sub _ continuous_const,
    exact hb.comp continuous_fst },
  have hδx₀ : ∀ t s, δ x₀ t s = γ t s,
  { intros t s, simp only [add_zero, loop.shift_apply, sub_self] },
  have hδs0 : ∀ x t, δ x t 0 = b x,
  { intros x t, simp only [h2γ, loop.shift_apply, add_sub_cancel'_right] },
  have hδt0 : ∀ x s, δ x 0 s = b x,
  { intros x t, simp only [h3γ, loop.shift_apply, add_sub_cancel'_right] },
  have hδΩ : ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) (s ∈ I), (x, δ x t s) ∈ Ω,
  { rcases hΩ_op with ⟨U, hUx₀, hU⟩,
    -- todo: this is nicer with `is_compact.eventually_forall_of_forall_eventually` twice, but then
    -- we need the continuity of `δ` with the arguments reassociated differently.
    have : ∀ᶠ (x : E) in 𝓝 x₀, ∀ (ts : ℝ × ℝ), ts ∈ set.prod I I → (x, δ x ts.1 ts.2) ∈ Ω,
    { refine is_compact.eventually_forall_mem (is_compact_Icc.prod is_compact_Icc)
        (continuous_fst.prod_mk hδ) _,
      rintro ⟨t, s⟩ ⟨ht, hs⟩,
      rw [hδx₀],
      show Ω ∈ 𝓝 (x₀, γ t s),
      exact mem_nhds_iff.mpr
        ⟨_, inter_subset_left _ _, hU, ⟨h4γ t s, show x₀ ∈ U, from mem_of_mem_nhds hUx₀⟩⟩ },
    refine this.mono _, intros x h t ht s hs, exact h (t, s) ⟨ht, hs⟩ },
  have hδsurr : ∀ᶠ x in 𝓝 x₀, (δ x 1).surrounds (g x),
  { rcases h5γ with ⟨p, w, h⟩,
    obtain ⟨W, hW⟩ := smooth_surrounding_pts h,
    let c : E → F × (fin (d+1) → F) := λ x, (g x, δ x 1 ∘ p),
    have hc : continuous_at c x₀ := hg.prod
      (continuous_at_const.add $ (continuous_at_pi.2 (λ _, hbx₀)).sub continuous_at_const),
    have hcx₀ : c x₀ = (g x₀, γ 1 ∘ p),
    { simp only [c, hδx₀, function.comp, prod.mk.inj_iff, eq_self_iff_true, and_self] },
    rw [← hcx₀] at hW,
    filter_upwards [hc.eventually hW], rintro x ⟨hW, hx⟩,
    exact ⟨_, _, hx⟩ },
  exact ⟨δ, _, hδΩ.and hδsurr, ⟨⟨hδs0, hδt0, λ x, and.right, hδ⟩, λ x, and.left⟩⟩
end

/-- Function used in `satisfied_or_refund`. Rename. -/
def ρ (t : ℝ) : ℝ := max 0 $ min 1 $ 2 * (1 - t)

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

lemma ρ_zero : ρ 0 = 1 := by simp
lemma ρ_half : ρ 2⁻¹ = 1 := by simp
lemma ρ_one : ρ 1 = 0 := by simp
lemma ρ_mem_I {x : ℝ} : ρ x ∈ I :=
⟨le_max_left _ _, max_le zero_le_one $ min_le_left _ _⟩

section satisfied_or_refund

variables {γ₀ γ₁ : E → ℝ → loop F}
variables (h₀ : surrounding_family g b γ₀ U) (h₁ : surrounding_family g b γ₁ U)

/-- The homotopy of surrounding families of loops used in lemma `satisfied_or_refund`.
  Having this as a separate definition is useful, because the construction actually gives some
  more information about the homotopy than the theorem `satisfied_or_refund` gives. -/
def sf_homotopy (τ : ℝ) (x : E) (t : ℝ) :=
loop.of_path $ (h₀.path x $ ρ τ * t).strans (h₁.path x $ ρ (1 - τ) * t)
  (set.proj_Icc 0 1 zero_le_one (1 - τ))

variables {h₀ h₁}

@[simp] lemma sf_homotopy_zero : sf_homotopy h₀ h₁ 0 = γ₀ :=
begin
  ext x t s,
  simp only [sf_homotopy, one_mul, ρ_eq_one_of_nonpos, surrounding_family.path_extend_fract,
    sub_zero, loop.of_path_apply, unit_interval.mk_one, proj_Icc_right, path.strans_one]
end

@[simp] lemma sf_homotopy_one : sf_homotopy h₀ h₁ 1 = γ₁ :=
begin
  ext x t s,
  simp only [sf_homotopy, path.strans_zero, unit_interval.mk_zero, one_mul, ρ_eq_one_of_nonpos,
    surrounding_family.path_extend_fract, proj_Icc_left, loop.of_path_apply, sub_self]
end

lemma _root_.continuous.sf_homotopy {X : Type*} [uniform_space X]
  [separated_space X] [locally_compact_space X]
  {τ t s : X → ℝ} {f : X → E} (hτ : continuous τ) (hf : continuous f) (ht : continuous t)
  (hs : continuous s) : continuous (λ x, sf_homotopy h₀ h₁ (τ x) (f x) (t x) (s x)) :=
begin
  refine continuous.of_path _ _ _ _ hs,
  refine continuous.path_strans _ _ _ _ _ continuous_snd,
  { refine h₀.continuous_path (hf.comp continuous_fst.fst) _ continuous_snd,
    exact (continuous_ρ.comp $ hτ.comp continuous_fst.fst).mul (ht.comp continuous_fst.fst) },
  { refine h₁.continuous_path (hf.comp continuous_fst.fst) _ continuous_snd,
    refine (continuous_ρ.comp _).mul (ht.comp continuous_fst.fst),
    exact continuous_const.sub (hτ.comp continuous_fst.fst) },
  { intros x s hs, simp only [proj_Icc_eq_zero, sub_nonpos] at hs,
    simp only [hs, h₀.t₀, zero_mul, surrounding_family.path_apply, ρ_eq_zero_of_le] },
  { intros x s hs, simp only [proj_Icc_eq_one] at hs,
    simp only [hs, h₁.t₀, zero_mul, surrounding_family.path_apply, ρ_eq_zero_of_le] },
  { refine continuous_proj_Icc.comp (continuous_const.sub (hτ.comp continuous_fst)) }
end

/-- In this lemmas and the lemmas below we add `finite_dimensional ℝ E` so that we can conclude
 `locally_compact_space E`. -/
lemma continuous_sf_homotopy [finite_dimensional ℝ E] : continuous ↿(sf_homotopy h₀ h₁) :=
continuous.sf_homotopy continuous_fst continuous_snd.fst continuous_snd.snd.fst
  continuous_snd.snd.snd

lemma surrounding_family_sf_homotopy [finite_dimensional ℝ E] (τ : ℝ) :
  surrounding_family g b (sf_homotopy h₀ h₁ τ) U :=
begin
  constructor,
  { intros x t, simp only [sf_homotopy, unit_interval.mk_zero, zero_le_one, extend_extends,
      path.source, loop.of_path_apply, left_mem_Icc, fract_zero] },
  { intros x s, simp only [sf_homotopy, surrounding_family.path_t₀, path.refl_strans_refl,
      path.refl_extend, loop.of_path_apply, mul_zero] },
  { intros x hx, cases le_total τ (1 / 2) with h h,
    { have : τ < 1 := h.trans_lt (by norm_num),
      refine (h₀.surrounds x hx).mono _,
      simp only [mul_one, loop.range_of_path, sf_homotopy],
      refine subset.trans (by simp only [surrounding_family.range_path, ρ_eq_one_of_le, h])
        (subset_range_strans_left $ by simp [this]) },
    { have : 0 < τ := lt_of_lt_of_le (by norm_num) h,
      have h : 1 - τ ≤ 1 / 2, { rw [sub_le], convert h, norm_num },
      refine (h₁.surrounds x hx).mono _,
      simp only [mul_one, loop.range_of_path, sf_homotopy],
      refine subset.trans (by simp only [surrounding_family.range_path, ρ_eq_one_of_le, h])
        (subset_range_strans_right $ by simp [this]) } },
  { exact continuous_const.sf_homotopy continuous_fst continuous_snd.fst continuous_snd.snd }
end

/-- A more precise version of `sf_homotopy_in`. -/
lemma sf_homotopy_in' {ι} (h₀ : surrounding_family g b γ₀ U) (h₁ : surrounding_family g b γ₁ U)
  (τ : ι → ℝ) (x : ι → E) (i : ι) {V : set E} (hx : x i ∈ V) {t : ℝ} (ht : t ∈ I) {s : ℝ}
  (h_in₀ : ∀ i (hx : x i ∈ V) (t ∈ I) (s : ℝ), τ i ≠ 1 → (x i, γ₀ (x i) t s) ∈ Ω)
  (h_in₁ : ∀ i (hx : x i ∈ V) (t ∈ I) (s : ℝ), τ i ≠ 0 → (x i, γ₁ (x i) t s) ∈ Ω) :
  (x i, sf_homotopy h₀ h₁ (τ i) (x i) t s) ∈ Ω :=
begin
  by_cases hτ0 : τ i = 0, { simp [hτ0], exact h_in₀ i hx t ht s (by norm_num [hτ0]) },
  by_cases hτ1 : τ i = 1, { simp [hτ1], exact h_in₁ i hx t ht s (by norm_num [hτ1]) },
  generalize hy : sf_homotopy h₀ h₁ (τ i) (x i) t s = y,
  have h2y : y ∈ range (sf_homotopy h₀ h₁ (τ i) (x i) t), { rw [← hy], exact mem_range_self _},
  rw [sf_homotopy, loop.range_of_path] at h2y,
  replace h2y := range_strans_subset h2y,
  rcases h2y with ⟨s', rfl⟩|⟨s', rfl⟩,
  { exact h_in₀ _ hx _ (unit_interval.mul_mem' ρ_mem_I ht) _ hτ1 },
  { exact h_in₁ _ hx _ (unit_interval.mul_mem' ρ_mem_I ht) _ hτ0 }
end

lemma sf_homotopy_in (h₀ : surrounding_family_in g b γ₀ U Ω) (h₁ : surrounding_family_in g b γ₁ U Ω)
  (τ : ℝ) ⦃x : E⦄ (hx : x ∈ U) {t : ℝ} (ht : t ∈ I) {s : ℝ} :
  (x, sf_homotopy h₀.to_sf h₁.to_sf τ x t s) ∈ Ω :=
sf_homotopy_in' h₀.to_sf h₁.to_sf (λ _, τ) (λ _, x) () hx ht
  (λ i hx t ht s _, h₀.val_in hx ht)
  (λ i hx t ht s _, h₁.val_in hx ht)

lemma surrounding_family_in_sf_homotopy [finite_dimensional ℝ E]
  (h₀ : surrounding_family_in g b γ₀ U Ω) (h₁ : surrounding_family_in g b γ₁ U Ω) (τ : ℝ) :
  surrounding_family_in g b (sf_homotopy h₀.to_sf h₁.to_sf τ) U Ω :=
⟨surrounding_family_sf_homotopy _, λ x hx t ht s hs, sf_homotopy_in _ _ _ hx ht⟩

lemma satisfied_or_refund [finite_dimensional ℝ E] {γ₀ γ₁ : E → ℝ → loop F}
  (h₀ : surrounding_family_in g b γ₀ U Ω) (h₁ : surrounding_family_in g b γ₁ U Ω) :
  ∃ γ : ℝ → E → ℝ → loop F,
    (∀ τ, surrounding_family_in g b (γ τ) U Ω) ∧
    γ 0 = γ₀ ∧
    γ 1 = γ₁ ∧
    continuous ↿γ :=
⟨sf_homotopy h₀.to_sf h₁.to_sf, surrounding_family_in_sf_homotopy h₀ h₁, sf_homotopy_zero,
  sf_homotopy_one, continuous_sf_homotopy⟩

end satisfied_or_refund

lemma extends_loops [finite_dimensional ℝ E] {U₀ U₁ K₀ K₁ : set E} (hU₀ : is_open U₀)
  (hU₁ : is_open U₁) (hK₀ : is_compact K₀) (hK₁ : is_compact K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁)
  {γ₀ γ₁ : E → ℝ → loop F}
  (h₀ : surrounding_family_in g b γ₀ U₀ Ω) (h₁ : surrounding_family_in g b γ₁ U₁ Ω) :
  ∃ U ∈ nhds_set (K₀ ∪ K₁), ∃ γ : E → ℝ → loop F,
    surrounding_family_in g b γ U Ω ∧
    ∀ᶠ x in nhds_set K₀, γ x = γ₀ x :=
begin
  obtain ⟨V₀, hV₀, hKV₀, hVU₀, hcV₀⟩ := exists_open_between_and_is_compact_closure hK₀ hU₀ hKU₀,
  let L₁ := K₁ \ U₀,
  have hL₁ : is_compact L₁ := hK₁.diff hU₀,
  have hV₀L₁ : disjoint (closure V₀) L₁ := disjoint_diff.mono hVU₀ subset.rfl,
  obtain ⟨V₁, hV₁, hLV₁, h2V₁, hcV₁⟩ :=
  exists_open_between_and_is_compact_closure hL₁
    (hcV₀.is_closed.is_open_compl.inter hU₁)
    (subset_inter (disjoint_iff_subset_compl_left.mp hV₀L₁) $ (diff_subset _ _).trans hKU₁),
  rw [subset_inter_iff, ← disjoint_iff_subset_compl_left] at h2V₁,
  rcases h2V₁ with ⟨hV₀₁, hVU₁⟩,
  refine ⟨V₀ ∪ (U₁ ∩ U₀) ∪ V₁, ((hV₀.union $ hU₁.inter hU₀).union hV₁).mem_nhds_set.mpr _, _⟩,
  { refine union_subset (hKV₀.trans $ (subset_union_left _ _).trans $ subset_union_left _ _) _,
    rw [← inter_union_diff K₁], exact
      union_subset_union ((inter_subset_inter_left _ hKU₁).trans $ subset_union_right _ _) hLV₁ },
  obtain ⟨ρ, h0ρ, h1ρ, hρ⟩ :=
    exists_continuous_zero_one_of_closed hcV₀.is_closed hcV₁.is_closed hV₀₁,
  let h₀' : surrounding_family_in g b γ₀ (U₁ ∩ U₀) Ω := h₀.mono (inter_subset_right _ _),
  let h₁' : surrounding_family_in g b γ₁ (U₁ ∩ U₀) Ω := h₁.mono (inter_subset_left _ _),
  let γ := sf_homotopy h₀'.to_sf h₁'.to_sf,
  have hγ : ∀ τ, surrounding_family_in g b (γ τ) (U₁ ∩ U₀) Ω :=
    surrounding_family_in_sf_homotopy _ _,
  refine ⟨λ x t, γ (ρ x) x t, _, _⟩,
  { refine ⟨⟨λ x, (hγ $ ρ x).base x, λ x, (hγ $ ρ x).t₀ x, _, _⟩, _⟩,
    { rintro x ((hx|hx)|hx),
      { simp_rw [γ, h0ρ (subset_closure hx), pi.zero_apply, sf_homotopy_zero,
          h₀.surrounds x (hVU₀ $ subset_closure hx)] },
      { simp_rw [γ, (hγ $ ρ x).surrounds x hx] },
      { simp_rw [γ, h1ρ (subset_closure hx), pi.one_apply, sf_homotopy_one,
          h₁.surrounds x (hVU₁ $ subset_closure hx)] } },
    { exact continuous.sf_homotopy (ρ.continuous.comp continuous_fst) continuous_fst
        continuous_snd.fst continuous_snd.snd },
    { intros x hx t ht s _, sorry /-refine sf_homotopy_in' _ _ _ id _ hx ht _ _,
      { intros x hx t ht s hρx, refine h₀.val_in x _ t ht s, rcases hx with (hx|⟨-,hx⟩)|hx,
        { exact (subset_closure.trans hVU₀) hx },
        { exact hx },
        { exact (hρx $ h1ρ $ subset_closure hx).elim } },
      { intros x hx t ht s hρx, refine h₁.val_in x _ t ht s, rcases hx with (hx|⟨hx,-⟩)|hx,
        { exact (hρx $ h0ρ $ subset_closure hx).elim },
        { exact hx },
        { exact (subset_closure.trans hVU₁) hx } }-/ } },
  { refine eventually.mono (hV₀.mem_nhds_set.mpr hKV₀) (λ x (hx : x ∈ V₀), _),
    simp_rw [γ, h0ρ (subset_closure hx), pi.zero_apply, sf_homotopy_zero] },
end

lemma exists_surrounding_loops [finite_dimensional ℝ E]
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
begin
  rcases hγ₀_surr with ⟨V, hV, hγ₀⟩,
  rw [mem_nhds_set] at hV, rcases hV with ⟨U₀, hU₀, hKU₀, hU₀V⟩,
  obtain ⟨V₀, hV₀, hKV₀, hVU₀, hcV₀⟩ := exists_open_between_and_is_compact_closure hK hU₀ hKU₀,
  sorry
end

-- #print axioms satisfied_or_refund
-- #print axioms extends_loops
-- #lint
