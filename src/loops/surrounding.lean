import loops.basic
import tactic.fin_cases
import topology.metric_space.emetric_paracompact
import topology.shrinking_lemma

import to_mathlib.order.filter.eventually_constant

/-!
# Surrounding families of loops
-/

open set function finite_dimensional int prod function path filter topological_space
open_locale classical topological_space unit_interval big_operators

namespace is_path_connected
-- we redo `exists_path_through_family` to use `def`s

variables {X : Type*} [topological_space X] {F : set X}

/-- An arbitrary path joining `x` and `y` in `F`. -/
noncomputable def some_path (hF : is_path_connected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
  path x y :=
(hF.joined_in x hx y hy).some_path

lemma some_path_mem (hF : is_path_connected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F)
  (t : I) : hF.some_path hx hy t ∈ F :=
joined_in.some_path_mem _ t

lemma range_some_path_subset (hF : is_path_connected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
  range (hF.some_path hx hy) ⊆ F :=
by { rintro _ ⟨t, rfl⟩, apply some_path_mem }

/-- A path through `p 0`, ..., `p n`. Usually this is used with `n := m`. -/
noncomputable def path_through (hF : is_path_connected F) {m : ℕ} {p : fin (m+1) → X}
  (hp : ∀ i, p i ∈ F) : ∀ n : ℕ, path (p 0) (p n)
| 0     := path.refl (p 0)
| (n+1) := (path_through n).trans $ hF.some_path (hp _) (hp _)

attribute [simp] path.trans_range
lemma range_path_through_subset (hF : is_path_connected F) {m : ℕ} {p : fin (m+1) → X}
  (hp : ∀ i, p i ∈ F) : ∀ {n : ℕ}, range (hF.path_through hp n) ⊆ F
| 0     := by simp [path_through, hp]
| (n+1) := by simp [path_through, hp, range_some_path_subset, @range_path_through_subset n]

lemma mem_range_path_through' (hF : is_path_connected F) {m : ℕ} {p : fin (m+1) → X}
  (hp : ∀ i, p i ∈ F) {i n : ℕ} (h : i ≤ n) : p i ∈ range (hF.path_through hp n) :=
begin
  induction h with n hn ih,
  { exact ⟨1, by simp⟩ },
  { simp only [path_through, path.trans_range, mem_union, ih, true_or] }
end

lemma mem_range_path_through (hF : is_path_connected F) {m : ℕ} {p : fin (m+1) → X}
  (hp : ∀ i, p i ∈ F) {i : fin (m+1)} : p i ∈ range (hF.path_through hp m) :=
by { convert hF.mem_range_path_through' hp (nat.le_of_lt_succ i.2), simp }

end is_path_connected

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

local notation `d` := finrank ℝ F
local notation `smooth_on` := times_cont_diff_on ℝ ⊤

/-- `f` is smooth at `x` if `f` is smooth on some neighborhood of `x`. -/
def smooth_at (f : E → F) (x : E) : Prop := ∃ s ∈ 𝓝 x, smooth_on f s

lemma smooth_at.continuous_at {f : E → F} {x : E} (h : smooth_at f x) : continuous_at f x :=
by { obtain ⟨s, hs, h⟩ := h, exact h.continuous_on.continuous_at hs }

section surrounding_points

local notation `ι` := fin (d + 1)

-- def:surrounds_points
/-- `p` is a collection of points surrounding `f` with weights `w` (that are positive and sum to 1)
if the weighted average of the points `p` is `f` and the points `p` form an affine basis of the
space. -/
structure surrounding_pts (f : F) (p : ι → F) (w : ι → ℝ) : Prop :=
(indep : affine_independent ℝ p)
(w_pos : ∀ i, 0 < w i)
(w_sum : ∑ i, w i = 1)
(avg : ∑ i, w i • p i = f)

lemma surrounding_pts.tot [finite_dimensional ℝ F]
  {f : F} {p : ι → F} {w : ι → ℝ} (h : surrounding_pts f p w) :
  affine_span ℝ (range p) = ⊤ :=
h.indep.affine_span_eq_top_iff_card_eq_finrank_add_one.mpr (fintype.card_fin _)

lemma surrounding_pts.coord_eq_w [finite_dimensional ℝ F]
  {f : F} {p : ι → F} {w : ι → ℝ} (h : surrounding_pts f p w) :
  (⟨p, h.indep, h.tot⟩ : affine_basis ι ℝ F).coords f = w :=
begin
  let b : affine_basis ι ℝ F := ⟨p, h.indep, h.tot⟩,
  change b.coords f = w,
  ext i,
  rw [← h.avg, ← finset.univ.affine_combination_eq_linear_combination _ w h.w_sum, affine_basis.coords_apply],
  exact affine_basis.coord_apply_combination_of_mem _ (finset.mem_univ i) h.w_sum,
end

/-- `f` is surrounded by a set `s` if there is an affine basis `p` in `s` with weighted average `f`.
-/
def surrounded (f : F) (s : set F) : Prop :=
∃ p w, surrounding_pts f p w ∧ ∀ i, p i ∈ s

lemma surrounded_iff_mem_interior_convex_hull_aff_basis [finite_dimensional ℝ F]
  {f : F} {s : set F} :
  surrounded f s ↔ ∃ (b : set F)
                     (h₀ : b ⊆ s)
                     (h₁ : affine_independent ℝ (coe : b → F))
                     (h₂ : affine_span ℝ b = ⊤),
                     f ∈ interior (convex_hull ℝ b) :=
begin
  split,
  { rintros ⟨p, w, ⟨⟨indep, w_pos, w_sum, rfl⟩, h_mem⟩⟩,
    have h_tot : affine_span ℝ (range p) = ⊤ :=
      indep.affine_span_eq_top_iff_card_eq_finrank_add_one.mpr (fintype.card_fin _),
    refine ⟨range p, range_subset_iff.mpr h_mem, indep.range, h_tot, _⟩,
    let basis : affine_basis ι ℝ F := ⟨p, indep, h_tot⟩,
    rw interior_convex_hull_aff_basis basis,
    intros i,
    rw [← finset.affine_combination_eq_linear_combination _ _ _ w_sum,
      basis.coord_apply_combination_of_mem (finset.mem_univ i) w_sum],
    exact w_pos i, },
  { rintros ⟨b, h₀, h₁, h₂, h₃⟩,
    haveI : fintype b := (finite_of_fin_dim_affine_independent ℝ h₁).fintype,
    have hb : fintype.card b = d + 1,
    { rw [← h₁.affine_span_eq_top_iff_card_eq_finrank_add_one, subtype.range_coe_subtype,
        set_of_mem_eq, h₂], },
    let p := (coe : _ → F) ∘ (fintype.equiv_fin_of_card_eq hb).symm,
    have hp : b = range p,
    { ext x,
      exact ⟨by { intros h, use fintype.equiv_fin_of_card_eq hb ⟨x, h⟩, simp [p], },
             by { rintros ⟨y, rfl⟩, apply subtype.coe_prop, }⟩, },
    rw hp at h₀ h₂ h₃,
    replace h₁ : affine_independent ℝ p :=
      h₁.comp_embedding (fintype.equiv_fin_of_card_eq hb).symm.to_embedding,
    let basis : affine_basis ι ℝ F := ⟨_, h₁, h₂⟩,
    rw [interior_convex_hull_aff_basis basis, mem_set_of_eq] at h₃,
    refine ⟨p, λ i, basis.coord i f, ⟨h₁, h₃, _, _⟩, λ i, h₀ (mem_range_self i)⟩,
    { exact basis.sum_coord_apply_eq_one f, },
    { rw [← finset.univ.affine_combination_eq_linear_combination p _
        (basis.sum_coord_apply_eq_one f),
        basis.affine_combination_coord_eq_self] } }
end

--- lem:int_cvx
lemma surrounded_of_convex_hull [finite_dimensional ℝ F]
  {f : F} {s : set F} (hs : is_open s) (hsf : f ∈ convex_hull ℝ s) :
  surrounded f s :=
begin
  rw surrounded_iff_mem_interior_convex_hull_aff_basis,
  obtain ⟨t, hts, hai, hf⟩ :=
    (by simpa only [exists_prop, mem_Union] using convex_hull_eq_union.subst hsf :
    ∃ (t : finset F), (t : set F) ⊆ s ∧ affine_independent ℝ (coe : t → F) ∧
      f ∈ convex_hull ℝ (t : set F)),
  have htne : (t : set F).nonempty := (@convex_hull_nonempty_iff ℝ _ _ _ _ _).mp ⟨f, hf⟩,
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ :=
    exists_subset_affine_independent_span_eq_top_of_open hs hts htne hai,
  have hb₀ : b.finite, { exact finite_of_fin_dim_affine_independent ℝ hb₃, },
  obtain ⟨c, hc⟩ := interior_convex_hull_nonempty_iff_aff_span_eq_top.mpr hb₄,
  obtain ⟨ε, hε, hcs⟩ := homothety_image_subset_of_open c hs hb₂ hb₀,
  have hbε := convex.subset_interior_image_homothety_of_one_lt
    (convex_convex_hull ℝ _) hc (1 + ε) (lt_add_of_pos_right 1 hε),
  rw affine_map.image_convex_hull at hbε,
  let t : units ℝ := units.mk0 (1 + ε) (by linarith),
  refine ⟨affine_map.homothety c (t : ℝ) '' b, hcs, _, _, hbε (convex_hull_mono hb₁ hf)⟩,
  { rwa (affine_equiv.homothety_units_mul_hom c t).affine_independent_set_of_eq_iff, },
  { exact (affine_equiv.homothety_units_mul_hom c t).span_eq_top_iff.mp hb₄, },
end

-- lem:smooth_barycentric_coord
lemma smooth_surrounding [finite_dimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
  (h : surrounding_pts x p w) :
  ∃ W : F → (ι → F) → (ι → ℝ),
  ∀ᶠ (yq : F × (ι → F)) in 𝓝 (x, p), smooth_at (uncurry W) yq ∧
                             (∀ i, 0 < W yq.1 yq.2 i) ∧
                             ∑ i, W yq.1 yq.2 i = 1 ∧
                             ∑ i, W yq.1 yq.2 i • yq.2 i = yq.1 :=
begin
  classical,
  use eval_barycentric_coords ι ℝ F,
  let V : set (ι → ℝ) := set.pi set.univ (λ i, Ioi (0 : ℝ)),
  let W' : F × (ι → F) → (ι → ℝ) := uncurry (eval_barycentric_coords ι ℝ F),
  let A : set (F × (ι → F)) := univ ×ˢ affine_bases ι ℝ F,
  let U : set (F × (ι → F)) := A ∩ (W' ⁻¹' V),
  have hι : fintype.card ι = d + 1 := fintype.card_fin _,
  have hp : p ∈ affine_bases ι ℝ F := ⟨h.indep, h.tot⟩,
  have hV : is_open V := is_open_set_pi finite_univ (λ _ _, is_open_Ioi),
  have hW' : continuous_on W' A := (smooth_barycentric ι ℝ F hι).continuous_on,
  have hxp : W' (x, p) ∈ V, { simp [W', hp, h.coord_eq_w, h.w_pos], },
  have hA : is_open A,
  { simp only [A, affine_bases_findim ι ℝ F hι],
    exact is_open_univ.prod (is_open_set_affine_independent ℝ F), },
  have hU₁ : U ⊆ A := set.inter_subset_left _ _,
  have hU₂ : is_open U := hW'.preimage_open_of_open hA hV,
  have hU₃ : U ∈ 𝓝 (x, p) :=
    mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, set.mem_inter (by simp [hp]) (mem_preimage.mpr hxp)⟩,
  apply eventually_of_mem hU₃,
  rintros ⟨y, q⟩ hyq,
  have hq : q ∈ affine_bases ι ℝ F, { simpa using hU₁ hyq, },
  have hyq' : (y, q) ∈ W' ⁻¹' V := (set.inter_subset_right _ _) hyq,
  refine ⟨⟨U, mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, hyq⟩, (smooth_barycentric ι ℝ F hι).mono hU₁⟩, _, _, _⟩,
  { simpa using hyq', },
  { simp [hq], },
  { simp [hq, affine_basis.linear_combination_coord_eq_self _ y], },
end

lemma smooth_surrounding_pts [finite_dimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
  (h : surrounding_pts x p w) :
  ∃ W : F → (ι → F) → (ι → ℝ),
  ∀ᶠ (yq : F × (ι → F)) in 𝓝 (x, p), smooth_at (uncurry W) yq ∧
    surrounding_pts yq.1 yq.2 (W yq.1 yq.2) :=
begin
  refine exists_imp_exists (λ W hW, _) (smooth_surrounding h),
  rw [nhds_prod_eq] at hW ⊢,
  have := (is_open.eventually_mem (is_open_set_affine_independent ℝ F) h.indep).prod_inr (𝓝 x),
  filter_upwards [hW, this], rintro ⟨y, q⟩ ⟨hW, h2W, h3W, hq⟩ h2q,
  exact ⟨hW, h2q, h2W, h3W, hq⟩
end

end surrounding_points

namespace loop

variables {γ γ' : loop F} {x y : F} {t : ℝ}

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def surrounds (γ : loop F) (x : F) : Prop :=
  ∃ t w : fin (d + 1) → ℝ, surrounding_pts x (γ ∘ t) w

lemma surrounds_iff_range_subset_range :
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

lemma affine_equiv_surrounds_iff (e : F ≃ᵃ[ℝ] F) :
  γ.surrounds x ↔ (γ.transform e).surrounds (e x) :=
begin
  suffices : ∀ (γ : loop F) x (e : F ≃ᵃ[ℝ] F), γ.surrounds x → (γ.transform e).surrounds (e x),
  { refine ⟨this γ x e, λ h, _⟩,
    specialize this (γ.transform e) (e x) e.symm h,
    rw affine_equiv.symm_apply_apply at this,
    convert this,
    ext,
    simp, },
  rintros γ x e ⟨t, w, indep, w_pos, w_sum, rfl⟩,
  refine ⟨t, w, ⟨e.affine_independent_iff.mpr indep, w_pos, w_sum, _⟩⟩,
  simp only [← finset.affine_combination_eq_linear_combination _ _ _ w_sum],
  erw finset.map_affine_combination _ (γ ∘ t) _ w_sum (e : F →ᵃ[ℝ] F),
  congr,
end

lemma vadd_surrounds : γ.surrounds x ↔ (y +ᵥ γ).surrounds (y + x) :=
begin
  rw add_comm,
  convert affine_equiv_surrounds_iff (affine_equiv.vadd_const ℝ y),
  ext u,
  simp [add_comm y],
end

lemma surrounds.vadd (h : γ.surrounds x) : (y +ᵥ γ).surrounds (y + x) :=
vadd_surrounds.mp h

lemma surrounds.vadd0 (h : γ.surrounds 0) : (y +ᵥ γ).surrounds y :=
by { convert h.vadd, rw [add_zero] }

lemma surrounds.smul0 (h : γ.surrounds 0) (ht : t ≠ 0) : (t • γ).surrounds 0 :=
begin
  rw [affine_equiv_surrounds_iff (affine_equiv.homothety_units_mul_hom (0 : F) (units.mk0 t ht)⁻¹),
    affine_equiv.coe_homothety_units_mul_hom_apply, affine_map.homothety_apply_same],
  convert h,
  ext u,
  simp [affine_map.homothety_apply, smul_smul, inv_mul_cancel ht],
end

lemma surrounds.mono (h : γ.surrounds x) (h2 : range γ ⊆ range γ') : γ'.surrounds x :=
begin
  revert h, simp_rw [loop.surrounds_iff_range_subset_range],
  refine exists_imp_exists (λ t, _),
  refine exists_imp_exists (λ w, _),
  exact and.imp_right (λ h3, subset.trans h3 h2),
end

end loop

section surrounding_loop

variables {O : set F} {f b : F} {p : fin (d + 1) → F}
  (O_conn : is_path_connected O)
  (hp : ∀ i, p i ∈ O)
  (hb : b ∈ O)

/-- witness of `surrounding_loop_of_convex_hull` -/
def surrounding_loop : ℝ → loop F :=
loop.round_trip_family $ (O_conn.some_path hb (hp 0)).trans $ O_conn.path_through hp d

variables {O_conn hp hb}

/-- TODO: continuity note -/
lemma continuous_surrounding_loop : continuous ↿(surrounding_loop O_conn hp hb) :=
loop.round_trip_family_continuous

@[simp] lemma surrounding_loop_zero_right (t : ℝ) : surrounding_loop O_conn hp hb t 0 = b :=
loop.round_trip_family_based_at t

@[simp] lemma surrounding_loop_zero_left (s : ℝ) : surrounding_loop O_conn hp hb 0 s = b :=
by { simp only [surrounding_loop, loop.round_trip_family_zero], refl }

lemma surrounding_loop_mem (t s : ℝ) : surrounding_loop O_conn hp hb t s ∈ O :=
begin
  revert s,
  rw ← range_subset_iff,
  simp only [surrounding_loop, loop.round_trip_family, path.trans_range, loop.round_trip_range,
    cast_coe],
  refine subset.trans (truncate_range _) _,
  simp only [trans_range, union_subset_iff, O_conn.range_some_path_subset,
    O_conn.range_path_through_subset, true_and]
end

lemma surrounding_loop_surrounds {w : fin (d + 1) → ℝ} (h : surrounding_pts f p w) :
  (surrounding_loop O_conn hp hb 1).surrounds f :=
begin
  rw loop.surrounds_iff_range_subset_range,
  refine ⟨p, w, h, _⟩,
  simp only [surrounding_loop, loop.round_trip_family_one, loop.round_trip_range, trans_range,
    range_subset_iff, mem_union, O_conn.mem_range_path_through, or_true, forall_true_iff]
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
  rcases O_conn.joined_in b hb (p 0) (hp 0) with ⟨Ω₁, hΩ₁⟩,
  exact ⟨surrounding_loop O_conn hp hb, continuous_surrounding_loop, surrounding_loop_zero_right,
    surrounding_loop_zero_left, surrounding_loop_mem, surrounding_loop_surrounds h⟩
end

end surrounding_loop

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

variables {g b : E → F} {U K C : set E} {Ω : set (E × F)}

namespace surrounding_family_in

variables {γ : E → ℝ → loop F}

/-- Abbreviation for `to_surrounding_family` -/
lemma to_sf (h : surrounding_family_in g b γ U Ω) : surrounding_family g b γ U :=
h.to_surrounding_family

lemma val_in (h : surrounding_family_in g b γ U Ω) {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ I)
  {s : ℝ} : (x, γ x t s) ∈ Ω :=
by { rw [← loop.fract_eq], exact h.val_in' x hx t ht (fract s) (unit_interval.fract_mem s) }

protected lemma mono (h : surrounding_family_in g b γ U Ω) {V : set E} (hVU : V ⊆ U) :
  surrounding_family_in g b γ V Ω :=
⟨h.to_sf.mono hVU, λ x hx, h.val_in' x (hVU hx)⟩

end surrounding_family_in

section local_loops
variables {x₀ : E} (hΩ_conn : is_path_connected (prod.mk x₀ ⁻¹' Ω))
  (hb_in : (x₀, b x₀) ∈ Ω)
  {p : fin (d + 1) → F}
  (hp : ∀ i, p i ∈ prod.mk x₀ ⁻¹' Ω)

/-- The witness of `local_loops`. -/
def local_loops_def (x : E) (t : ℝ) : loop F :=
b x - b x₀ +ᵥ surrounding_loop hΩ_conn hp hb_in t

/--
Note: The conditions in this lemma are currently a bit weaker than the ones mentioned in the
blueprint.
TODO: use `local_loops_def`
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
  let δ : E → ℝ → loop F := λ x t, b x - b x₀ +ᵥ γ t,
  have hδ : continuous ↿δ,
  { dsimp only [δ, has_uncurry.uncurry, loop.vadd_apply],
    refine continuous.add _ (h1γ.comp continuous_snd),
    refine continuous.sub _ continuous_const,
    exact hb.comp continuous_fst },
  have hδx₀ : ∀ t s, δ x₀ t s = γ t s,
  { intros t s, simp only [zero_add, loop.vadd_apply, sub_self] },
  have hδs0 : ∀ x t, δ x t 0 = b x,
  { intros x t, simp only [h2γ, loop.vadd_apply, sub_add_cancel] },
  have hδt0 : ∀ x s, δ x 0 s = b x,
  { intros x t, simp only [h3γ, loop.vadd_apply, sub_add_cancel] },
  have hδΩ : ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) (s ∈ I), (x, δ x t s) ∈ Ω,
  { rcases hΩ_op with ⟨U, hUx₀, hU⟩,
    -- todo: this is nicer with `is_compact.eventually_forall_of_forall_eventually` twice, but then
    -- we need the continuity of `δ` with the arguments reassociated differently.
    have : ∀ᶠ (x : E) in 𝓝 x₀, ∀ (ts : ℝ × ℝ), ts ∈ I ×ˢ I → (x, δ x ts.1 ts.2) ∈ Ω,
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
      (((continuous_at_pi.2 (λ _, hbx₀)).sub continuous_at_const).add continuous_at_const),
    have hcx₀ : c x₀ = (g x₀, γ 1 ∘ p),
    { simp only [c, hδx₀, function.comp, prod.mk.inj_iff, eq_self_iff_true, and_self] },
    rw [← hcx₀] at hW,
    filter_upwards [hc.eventually hW], rintro x ⟨hW, hx⟩,
    exact ⟨_, _, hx⟩ },
  exact ⟨δ, _, hδΩ.and hδsurr, ⟨⟨hδs0, hδt0, λ x, and.right, hδ⟩, λ x, and.left⟩⟩
end

/-- A tiny reformulation of `local_loops` where the existing `U` is open. -/
lemma local_loops_open [finite_dimensional ℝ F]
  {x₀ : E}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ fst ⁻¹' U))
  (hΩ_conn : is_connected (prod.mk x₀ ⁻¹' Ω))
  (hg : continuous_at g x₀) (hb : continuous b)
  (hb_in : (x₀, b x₀) ∈ Ω)
  (hconv : g x₀ ∈ convex_hull ℝ (prod.mk x₀ ⁻¹' Ω)) :
  ∃ (γ : E → ℝ → loop F) (U : set E), is_open U ∧ x₀ ∈ U ∧ surrounding_family_in g b γ U Ω :=
begin
  obtain ⟨γ, U, hU, hγ⟩ := local_loops hΩ_op hΩ_conn hg hb hb_in hconv,
  obtain ⟨V, hVU, hV, hx₀V⟩ := mem_nhds_iff.mp hU,
  exact ⟨γ, V, hV, hx₀V, hγ.mono hVU⟩
end

end local_loops

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

section extend_loops

variables [finite_dimensional ℝ E]

/-- Loop data consists of a compact subset of a surrounding family on an open set `U`, with a
  specified compact subset `K`. -/
@[nolint has_inhabited_instance]
structure loop_data (g b : E → F) (Ω : set (E × F)) :=
(K U : set E)
(γ :  E → ℝ → loop F)
(hK : is_compact K)
(hU : is_open U)
(hKU : K ⊆ U)
(hγ : surrounding_family_in g b γ U Ω)

/-
Note: we also want add the condition that `γ = γ₀` outside a neighborhood of `U₁ᶜ`.
This makes it easier to find the limit of a sequence of these constructions.
Todo: we might need that `γ = γ₀` on a neighborhood of `(U₀ ∪ U₁)ᶜ` to ensure that
`(U₀ ∪ U₁)ᶜ ⊆ extended_invariant ...`
-/
lemma extend_loops {U₀ U₁ K₀ K₁ : set E} (hU₀ : is_open U₀) (hU₁ : is_open U₁)
  (hK₀ : is_compact K₀) (hK₁ : is_compact K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁)
  {γ₀ γ₁ : E → ℝ → loop F}
  (h₀ : surrounding_family_in g b γ₀ U₀ Ω) (h₁ : surrounding_family_in g b γ₁ U₁ Ω) :
  ∃ (U ∈ 𝓝ˢ (K₀ ∪ K₁)) (γ : E → ℝ → loop F),
    surrounding_family_in g b γ U Ω ∧
    (∀ᶠ x in 𝓝ˢ K₀, γ x = γ₀ x) ∧
    (∀ᶠ x in 𝓝ˢ U₁ᶜ, γ x = γ₀ x) :=
begin
  obtain ⟨V₀, hV₀, hKV₀, hVU₀, hcV₀⟩ := exists_open_between_and_is_compact_closure hK₀ hU₀ hKU₀,
  let L₁ := K₁ \ U₀,
  have hL₁ : is_compact L₁ := hK₁.diff hU₀,
  have hV₀L₁ : disjoint (closure V₀) L₁ := disjoint_diff.mono hVU₀ subset.rfl,
  obtain ⟨V₂, hV₂, hLV₂, h2V₂, hcV₂⟩ :=
  exists_open_between_and_is_compact_closure hL₁
    (hcV₀.is_closed.is_open_compl.inter hU₁)
    (subset_inter (disjoint_iff_subset_compl_left.mp hV₀L₁) $ (diff_subset _ _).trans hKU₁),
  obtain ⟨V₁, hV₁, hLV₁, hV₁₂, hcV₁⟩ :=
    exists_open_between_and_is_compact_closure hL₁ hV₂ hLV₂,
  rw [subset_inter_iff, ← disjoint_iff_subset_compl_left] at h2V₂,
  rcases h2V₂ with ⟨hV₀₂, hV₂U₁⟩,
  have hVU₁ : V₁ ⊆ U₁ := subset_closure.trans (hV₁₂.trans $ subset_closure.trans hV₂U₁),
  have hdisj : disjoint (closure V₀ ∪ V₂ᶜ) (closure V₁),
  { refine disjoint.union_left (hV₀₂.mono_right (hV₁₂.trans subset_closure)) _,
    rw [disjoint_iff_subset_compl_left, compl_compl], exact hV₁₂ },
  refine ⟨V₀ ∪ (U₁ ∩ U₀) ∪ V₁, ((hV₀.union $ hU₁.inter hU₀).union hV₁).mem_nhds_set.mpr _, _⟩,
  { refine union_subset (hKV₀.trans $ (subset_union_left _ _).trans $ subset_union_left _ _) _,
    rw [← inter_union_diff K₁], exact
      union_subset_union ((inter_subset_inter_left _ hKU₁).trans $ subset_union_right _ _) hLV₁ },
  obtain ⟨ρ, h0ρ, h1ρ, hρ⟩ := exists_continuous_zero_one_of_closed
    (is_closed_closure.union hV₂.is_closed_compl) is_closed_closure hdisj,
  let h₀' : surrounding_family_in g b γ₀ (U₁ ∩ U₀) Ω := h₀.mono (inter_subset_right _ _),
  let h₁' : surrounding_family_in g b γ₁ (U₁ ∩ U₀) Ω := h₁.mono (inter_subset_left _ _),
  let γ := sf_homotopy h₀'.to_sf h₁'.to_sf,
  have hγ : ∀ τ, surrounding_family_in g b (γ τ) (U₁ ∩ U₀) Ω :=
    surrounding_family_in_sf_homotopy _ _,
  have heq1 : ∀ x ∈ closure V₀ ∪ V₂ᶜ, γ (ρ x) x = γ₀ x,
  { intros x hx, simp_rw [γ, h0ρ hx, pi.zero_apply, sf_homotopy_zero] },
  have heq2 : ∀ x ∈ V₀, γ (ρ x) x = γ₀ x :=
  λ x hx, heq1 x (subset_closure.trans (subset_union_left _ _) hx),
  refine ⟨λ x t, γ (ρ x) x t, _, _, _⟩,
  { refine ⟨⟨λ x, (hγ $ ρ x).base x, λ x, (hγ $ ρ x).t₀ x, _, _⟩, _⟩,
    { rintro x ((hx|hx)|hx),
      { simp_rw [heq2 x hx, h₀.surrounds x (hVU₀ $ subset_closure hx)] },
      { simp_rw [γ, (hγ $ ρ x).surrounds x hx] },
      { simp_rw [γ, h1ρ (subset_closure hx), pi.one_apply, sf_homotopy_one,
          h₁.surrounds x (hVU₁ hx)] } },
    { exact continuous.sf_homotopy (ρ.continuous.comp continuous_fst) continuous_fst
        continuous_snd.fst continuous_snd.snd },
    { intros x hx t ht s _, refine sf_homotopy_in' _ _ _ id _ hx ht _ _,
      { intros x hx t ht s hρx, refine h₀.val_in _ ht, rcases hx with (hx|⟨-,hx⟩)|hx,
        { exact (subset_closure.trans hVU₀) hx },
        { exact hx },
        { exact (hρx $ h1ρ $ subset_closure hx).elim } },
      { intros x hx t ht s hρx, refine h₁.val_in _ ht, rcases hx with (hx|⟨hx,-⟩)|hx,
        { exact (hρx $ h0ρ $ subset_closure.trans (subset_union_left _ _) hx).elim },
        { exact hx },
        { exact hVU₁ hx } } } },
  { exact eventually_of_mem (hV₀.mem_nhds_set.mpr hKV₀) heq2 },
  { refine eventually_of_mem
      (is_closed_closure.is_open_compl.mem_nhds_set.mpr $ compl_subset_compl.mpr hV₂U₁)
      (λ x hx, heq1 x $ mem_union_right _ $ compl_subset_compl.mpr subset_closure hx) },
end

/-! We now extract all components of this theorem, which makes them easier to use in the recursion
  in `exists_surrounding_loops` -/

/-- The domain of an arbitrary witness of `extend_loops`. -/
def extended_domain (l₀ l₁ : loop_data g b Ω) : set E :=
interior $ classical.some $ extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ

/-- An arbitrary witness of `extend_loops` with domain specified by `extended_domain`. -/
def extended_loops (l₀ l₁ : loop_data g b Ω) : E → ℝ → loop F :=
classical.some $ classical.some_spec $ classical.some_spec $
  extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ

/-- The (interior of the) set where `extended_loops` didn't change -/
def extended_invariant (l₀ l₁ : loop_data g b Ω) : set E :=
interior { x | extended_loops l₀ l₁ x = l₀.γ x }

variables {l₀ l₁ : loop_data g b Ω}

lemma is_open_extended_domain  : is_open (extended_domain l₀ l₁) :=
is_open_interior

lemma subset_extended_domain : l₀.K ∪ l₁.K ⊆ extended_domain l₀ l₁ :=
subset_interior_iff_mem_nhds_set.mpr $ classical.some $ classical.some_spec $
  extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ

lemma extended_domain_mem_nhds_set :
  extended_domain l₀ l₁ ∈ 𝓝ˢ (l₀.K ∪ l₁.K) :=
is_open_extended_domain.mem_nhds_set.mpr subset_extended_domain

lemma surrounding_family_extended_loops :
   surrounding_family_in g b (extended_loops l₀ l₁) (extended_domain l₀ l₁) Ω :=
(classical.some_spec $ classical.some_spec $ classical.some_spec $
  extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ).1.mono interior_subset

lemma is_open_extended_invariant : is_open (extended_invariant l₀ l₁) :=
is_open_interior

lemma subset_extended_invariant : l₀.K ⊆ extended_invariant l₀ l₁ :=
subset_interior_iff_mem_nhds_set.mpr
  (classical.some_spec $ classical.some_spec $ classical.some_spec $
    extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ).2.1

lemma compl_subset_extended_invariant : l₁.Uᶜ ⊆ extended_invariant l₀ l₁ :=
subset_interior_iff_mem_nhds_set.mpr
  (classical.some_spec $ classical.some_spec $ classical.some_spec $
    extend_loops l₀.hU l₁.hU l₀.hK l₁.hK l₀.hKU l₁.hKU l₀.hγ l₁.hγ).2.2

lemma extended_invariant_mem_nhds_set :
  extended_invariant l₀ l₁ ∈ 𝓝ˢ l₀.K :=
is_open_extended_invariant.mem_nhds_set.mpr subset_extended_invariant

lemma extended_loops_eq_left {x : E} (hx : x ∈ extended_invariant l₀ l₁) :
  extended_loops l₀ l₁ x = l₀.γ x :=
(interior_subset hx : _)

/-- `l₀.extend l₁` extends the `loop_data` `l₀` using `l₁`, making sure that the extended version
  is the same as `l₀` on a neighborhood of `l₀.K`. -/
def loop_data.extend (l₀ l₁ : loop_data g b Ω) : loop_data g b Ω :=
⟨l₀.K ∪ l₁.K, extended_domain l₀ l₁, extended_loops l₀ l₁, l₀.hK.union (l₁.hK),
  is_open_extended_domain, subset_extended_domain, surrounding_family_extended_loops⟩

end extend_loops

section surrounding_loops
variables [finite_dimensional ℝ E]

/-- Given a initial `loop_data` and a sequence of them, repeatedly extend `l₀` using `l`. -/
@[simp] noncomputable def loop_data_seq (l₀ : loop_data g b Ω) (l : ℕ → loop_data g b Ω) :
  ℕ → loop_data g b Ω
| 0     := l₀
| (n+1) := (loop_data_seq n).extend $ l n

variables {l₀ : loop_data g b Ω} {l : ℕ → loop_data g b Ω} {n : ℕ} {x y : E}

lemma loop_data_seq_succ_γ :
  (loop_data_seq l₀ l (n + 1)).γ = extended_loops (loop_data_seq l₀ l n) (l n) :=
by rw [loop_data_seq, loop_data.extend]

lemma loop_data_seq_K_mono : monotone (λ n, (loop_data_seq l₀ l n).K) :=
by { refine monotone_nat_of_le_succ _, intro n, rw [loop_data_seq], apply subset_union_left, }

lemma subset_loop_data_seq_K0 (n : ℕ) : l₀.K ⊆ (loop_data_seq l₀ l n).K :=
loop_data_seq_K_mono (zero_le n)

lemma subset_loop_data_seq_K : (l n).K ⊆ (loop_data_seq l₀ l (n+1)).K :=
subset_union_right _ _

lemma union_subset_loop_data_seq_K : l₀.K ∪ (⋃ n, (l n).K) ⊆ ⋃ n, (loop_data_seq l₀ l n).K :=
let K := λ n, (loop_data_seq l₀ l n).K in
union_subset (subset_Union K 0) $ Union_subset $
  λ n, subset_loop_data_seq_K.trans $ subset_Union K (n+1)

lemma eventually_mem_loop_data_seq_K (hx : x ∈ l₀.K ∪ (⋃ n, (l n).K)) :
  ∀ᶠ n in at_top, x ∈ (loop_data_seq l₀ l n).K :=
begin
  rcases union_subset_loop_data_seq_K hx with ⟨_, ⟨n, rfl⟩, hx⟩,
  exact eventually_at_top.mpr ⟨n, λ m hm, loop_data_seq_K_mono hm hx⟩
end

lemma loop_data_seq_locally_eventually_constant (l₀ : loop_data g b Ω)
  (hl : locally_finite (λ n, (l n).U)) :
  locally_eventually_constant_on (λ n, (loop_data_seq l₀ l n).γ) at_top univ :=
begin
  intros x hx,
  obtain ⟨O, hO, hWO⟩ := hl x,
  simp_rw [eventually_constant_on, ← eventually_constant_at_top_nat],
  use [O, hO, hWO.to_finset.sup id + 1],
  intros m hm, ext1 ⟨y, hy⟩,
  simp_rw [set.restrict_apply, subtype.coe_mk, loop_data_seq],
  apply extended_loops_eq_left,
  refine compl_subset_extended_invariant _,
  intro h2y,
  apply hm.not_lt,
  rw [nat.lt_add_one_iff],
  refine finset.le_sup (_ : m ∈ _),
  simp_rw [hWO.mem_to_finset, mem_set_of_eq],
  exact ⟨y, h2y, hy⟩
end

lemma loop_data_seq_eq0 (l₀ : loop_data g b Ω) (l : ℕ → loop_data g b Ω) (n : ℕ) :
  ∀ᶠ x in 𝓝ˢ l₀.K, (loop_data_seq l₀ l n).γ x = l₀.γ x :=
begin
  have : ∀ᶠ x in 𝓝ˢ l₀.K, ∀ m ∈ Iio n,
    (loop_data_seq l₀ l (m + 1)).γ x = (loop_data_seq l₀ l m).γ x,
  { rw [eventually_all_finite (finite_Iio n)], rintro m (hm : m < n),
    have : extended_invariant (loop_data_seq l₀ l m) (l m) ∈ 𝓝ˢ l₀.K,
    { refine is_open_extended_invariant.mem_nhds_set.mpr _,
      refine (loop_data_seq_K_mono (zero_le m)).trans subset_extended_invariant },
    refine eventually_of_mem this _,
    intros x hx, convert extended_loops_eq_left hx, rw [loop_data_seq_succ_γ] },
  refine this.mono (λ x hx, _), clear this,
  induction n with n ih,
  { refl, },
  { refine (hx _ $ lt_add_one n).trans (ih $ λ m hm, hx m $ lt_trans hm $ lt_add_one n) }
end

/-- The eventual value of the sequence `λ n, (loop_data_seq l₀ l).γ`. -/
def lim_loop (l₀ : loop_data g b Ω) (l : ℕ → loop_data g b Ω) (x : E) : ℝ → loop F :=
eventual_value (λ n, (loop_data_seq l₀ l n).γ x) at_top

/-- This gives only the pointwise behavior of `lim_loop`, use the interface for
  `eventually_constant_on` for the local behavior. -/
lemma exists_lim_loop_eq (l₀ : loop_data g b Ω) (l : ℕ → loop_data g b Ω)
  (hl : locally_finite (λ n, (l n).U)) (x : E) :
  ∃ N, lim_loop l₀ l x = (loop_data_seq l₀ l N).γ x :=
((loop_data_seq_locally_eventually_constant l₀ hl).eventually_constant $ mem_univ x)
  .exists_eventual_value_eq

lemma lim_loop_eq0 (hl : locally_finite (λ n, (l n).U))
  {K : set E} (hK : is_compact K) (h3K : K ⊆ l₀.K) :
  ∀ᶠ x in 𝓝ˢ K, lim_loop l₀ l x = l₀.γ x :=
begin
  obtain ⟨O, hO, h⟩ := (loop_data_seq_locally_eventually_constant l₀ hl)
    .exists_nhds_set_of_is_compact hK (subset_univ K),
  obtain ⟨n, hn⟩ := h.exists_eventual_value_eq,
  refine ((loop_data_seq_eq0 l₀ l n).filter_mono $ monotone_nhds_set $ h3K).mp _,
  refine eventually_of_mem hO _,
  intros x hx h2x,
  simp_rw [lim_loop, hn x hx, h2x]
end

lemma lim_surrounding_family_in (l₀ : loop_data g b Ω) (hl : locally_finite (λ n, (l n).U))
  (hU : U ⊆ l₀.K ∪ ⋃ n, (l n).K) :
  surrounding_family_in g b (lim_loop l₀ l) U Ω :=
begin
  have := loop_data_seq_locally_eventually_constant l₀ hl,
  refine ⟨⟨_, _, _, _⟩, _⟩,
  { intro x, obtain ⟨n, hn⟩ := exists_lim_loop_eq l₀ l hl x,
    simp_rw [hn], exact (loop_data_seq l₀ l n).hγ.base x },
  { intro x, obtain ⟨n, hn⟩ := exists_lim_loop_eq l₀ l hl x,
    simp_rw [hn], exact (loop_data_seq l₀ l n).hγ.t₀ x },
  { intros x hx,
    obtain ⟨n, h1n : (loop_data_seq l₀ l n).γ x = lim_loop l₀ l x,
      h2n : x ∈ (loop_data_seq l₀ l n).K⟩ :=
      ((eventually_eq_eventual_value
        (this.eventually_constant $ mem_univ x)).and $ eventually_mem_loop_data_seq_K (hU hx)).exists,
    rw [← h1n], refine (loop_data_seq l₀ l n).hγ.surrounds x ((loop_data_seq l₀ l n).hKU h2n) },
  { simp_rw [continuous_iff_continuous_at],
    rintro ⟨x, t, s⟩,
    obtain ⟨O, hO, hgO⟩ := this x (mem_univ x),
    obtain ⟨n, hn⟩ := (eventually_eq_eventual_value hgO).exists,
    dsimp at hn,
    simp only [function.funext_iff, eventual_value_apply hgO, restrict_apply, loop.ext_iff,
      set_coe.forall, subtype.coe_mk] at hn,
    refine (continuous_at_congr (eventually_of_mem (prod_is_open.mem_nhds hO univ_mem) _)).mp _,
    swap, { exact λ (x : E × ℝ × ℝ) hx, hn x.1 (mem_prod.2 hx).1 x.2.1 x.2.2 },
    exact (loop_data_seq l₀ l n).hγ.cont.continuous_at },
  { intros x hx,
    obtain ⟨n, h1n : (loop_data_seq l₀ l n).γ x = lim_loop l₀ l x,
      h2n : x ∈ (loop_data_seq l₀ l n).K⟩ :=
      ((eventually_eq_eventual_value
        (this.eventually_constant $ mem_univ x)).and $ eventually_mem_loop_data_seq_K (hU hx)).exists,
    rw [← h1n], refine (loop_data_seq l₀ l n).hγ.val_in' x ((loop_data_seq l₀ l n).hKU h2n) },
end

lemma exists_surrounding_loops [finite_dimensional ℝ F]
  (hK : is_compact K) (hC : is_closed C) (hU : is_open U) (hCU : C ⊆ U)
  (hΩ_op : is_open (Ω ∩ fst ⁻¹' U))
  (hΩ_conn : ∀ x ∈ C, is_connected (prod.mk x ⁻¹' Ω))
  (hg : ∀ x ∈ C, continuous_at g x) (hb : continuous b)
  (hb_in : ∀ x ∈ C, (x, b x) ∈ Ω)
  (hconv : ∀ x ∈ C, g x ∈ convex_hull ℝ (prod.mk x ⁻¹' Ω))
  {γ₀ :  E → ℝ → loop F}
  (hγ₀_surr : ∃ V ∈ 𝓝ˢ K, surrounding_family_in g b γ₀ V Ω) :
  ∃ γ : E → ℝ → loop F, surrounding_family_in g b γ C Ω ∧ ∀ᶠ x in 𝓝ˢ K, γ x = γ₀ x :=
begin
  /-
  Translation:
  Notes | Formalization
  ------+--------------
  γ     | γ₀
  U₀    | V
  Uᵢ    | W i
  Kᵢ    | L i
  cl(U) | C  -- C is the closure of U in the blueprint
  (-)   | U' -- an open neighborhood of C
  -/
  rcases hγ₀_surr with ⟨V, hV, hγ₀⟩,
  rw [mem_nhds_set_iff_exists] at hV, rcases hV with ⟨U₀, hU₀, hKU₀, hU₀V⟩,
  let P := λ N : set E, ∃ γ : E → ℝ → loop F, surrounding_family_in g b γ N Ω,
  have hP : antitone P, { rintro s t hst ⟨γ, hγ⟩, exact ⟨γ, hγ.mono hst⟩ },
  have h0P : P ∅ := ⟨γ₀, hγ₀.mono (empty_subset _)⟩,
  have h2P : ∀ x ∈ C, ∃ V ∈ 𝓝 x, P V,
  { intros x hx,
    obtain ⟨γ, W, hW, hxW, hγ⟩ := local_loops_open ⟨U, hU.mem_nhds $ hCU hx, hΩ_op⟩
     (hΩ_conn x hx) (hg x hx) hb (hb_in x hx) (hconv x hx),
    refine ⟨W, hW.mem_nhds hxW, γ, hγ⟩ },
  obtain ⟨L, W, hL, hW, hPW, hLW, hlW, hCL⟩ :=
    exists_locally_finite_subcover_of_locally hC hP h0P h2P,
  choose γ hγ using hPW,
  let l₀ : loop_data g b Ω :=
  ⟨K, U₀, γ₀, hK, hU₀, hKU₀, hγ₀.mono hU₀V⟩,
  let l : ℕ → loop_data g b Ω := λ n, ⟨L n, W n, γ n, hL n, hW n, hLW n, hγ n⟩,
  refine ⟨lim_loop l₀ l, lim_surrounding_family_in l₀ hlW (hCL.trans $ subset_union_right _ _),
    lim_loop_eq0 (hlW : _) hK subset.rfl⟩,
end

end surrounding_loops

-- #lint
-- #print axioms satisfied_or_refund
-- #print axioms extend_loops
-- #print axioms exists_surrounding_loops
