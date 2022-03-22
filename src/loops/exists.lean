import notations
import loops.reparametrization
import analysis.calculus.specific_functions
import to_mathlib.convolution


noncomputable theory

open set function finite_dimensional prod int topological_space metric
open measure_theory measure_theory.measure
open_locale topological_space unit_interval convolution


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F]
          {g b : E → F} {Ω : set (E × F)} {U K C : set E}
variables [normed_space ℝ F] [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

variables (g b Ω U K)

structure nice_loop (γ : ℝ → E → loop F) : Prop :=
(t_le_zero : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x)
(t_ge_one : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x)
(t_zero : ∀ x s, γ 0 x s = b x)
(s_zero : ∀ x t, γ t x 0 = b x)
(avg : ∀ x, (γ 1 x).average = g x)
(mem_Ω : ∀ x t s, (x, γ t x s) ∈ Ω)
(smooth : 𝒞 ∞ ↿γ)
(rel_K : ∀ᶠ x in 𝓝ˢ K, ∀ t s, γ t x s = b x)

variables {g b Ω U K}

/-- For every continuous positive function there is a smaller smooth positive function.

proof sketch: choose locally constant functions on compact sets, and patch them using a partition
of unity. -/
lemma exists_smooth_pos {f : E → ℝ} {U : set E} (hU : is_open U) (hf : continuous f)
  (h2f : ∀ x ∈ U, 0 < f x) :
  ∃ φ : E → ℝ, cont_diff ℝ ⊤ φ ∧ ∀ x ∈ U, 0 < φ x :=
sorry -- proof sketch:

lemma exists_loops [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω K γ  :=
begin
  let Om := λ x, hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x),
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_comp_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have op : ∀ x, is_open (prod.mk x ⁻¹' Ω),
   from λ x, hΩ_op.preimage (continuous.prod.mk x),

  -- choose a volume on E
  letI : measurable_space E := borel E,
  haveI : borel_space E := ⟨rfl⟩,
  letI K₀ : positive_compacts E,
  { refine ⟨⟨closed_ball 0 1, is_compact_closed_ball 0 1⟩, _⟩,
    rw [interior_closed_ball, nonempty_ball], all_goals { norm_num } },
  letI : measure_space E := ⟨add_haar_measure K₀⟩,
  -- haveI : is_add_haar_measure (volume : measure E) :=
  --   infer_instance,

  -- we could probably get away with something simpler to get γ₀.
  obtain ⟨γ₀, hγ₀_cont, hγ₀0, h2γ₀0, -, hγ₀_surr⟩ := -- γ₀ is γ* in notes
    surrounding_loop_of_convex_hull is_open_univ is_connected_univ
    (by { rw [convex_hull_univ], exact mem_univ 0 }) (mem_univ (0 : F)),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },
  have := λ x, local_loops_open ⟨univ, filter.univ_mem, h2Ω⟩ hg.continuous.continuous_at
    hb.continuous (hconv x),
  obtain ⟨ε, hε⟩ : { x : ℝ // 0 < x } := ⟨1, zero_lt_one⟩, -- todo
  let γ₁ : E → ℝ → loop F := λ x t, (γ₀ t).transform (λ y, b x + ε • y), -- `γ₁ x` is `γₓ` in notes
  have hγ₁ : ∃ V ∈ 𝓝ˢ K, surrounding_family_in g b γ₁ V Ω,
  { refine ⟨_, hgK, ⟨by simp [γ₁, hγ₀0], by simp [γ₁, h2γ₀0], _, _⟩, _⟩,
    { intros x hx, rw [mem_set_of_eq] at hx, rw [hx],
      exact (hγ₀_surr.smul0 hε.ne').vadd0 },
    { refine (hb.continuous.comp continuous_fst).add
        (continuous_const.smul $ hγ₀_cont.comp continuous_snd) },
    sorry }, -- choose ε sufficiently small, and pick V smaller
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK is_closed_univ is_open_univ subset.rfl h2Ω
    (λ x hx, hg.continuous.continuous_at) hb.continuous (λ x _, hconv x) hγ₁,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x t).reparam linear_reparam,
  let ε₁ : E → ℝ := λ x, ⨅ y : ℝ × ℝ, inf_dist (x, γ₂ x y.1 y.2) Ωᶜ, -- todo
  have hε₁ : continuous ε₁ := sorry, -- (continuous_inf_dist_pt _).comp (continuous_id.prod_mk hg.continuous),
  have h2ε₁ : ∀ {x}, 0 < ε₁ x, sorry,
  obtain ⟨ε₂, hε₂, h2ε₂⟩ := exists_smooth_pos is_open_univ hε₁ (λ x _, h2ε₁),
  have h2ε₂ : ∀ {x}, 0 < ε₂ x := λ x, h2ε₂ x (mem_univ _),
  let φ : E × ℝ × ℝ → ℝ :=
  λ x, (⟨⟨ε₂ x.1 / 2, ε₂ x.1, half_pos h2ε₂, half_lt_self h2ε₂⟩⟩ : cont_diff_bump (0 : E × ℝ × ℝ)) x,
  let γ₄ := ↿γ₃,
  let γ₅ : E × ℝ × ℝ → F := φ ⋆ γ₄,
  let γ₆ : ℝ → E → loop F,
  { refine λ s x, ⟨λ t, γ₅ (x, s, t), λ t, _⟩,
    change ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t + 1 - u.2.2) =
      ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t - u.2.2),
    simp_rw [← sub_add_eq_add_sub, (γ₃ _ _).per] },
  -- todo: apply reparametrization

  sorry
end
