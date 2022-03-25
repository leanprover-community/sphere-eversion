import geometry.manifold.partition_of_unity
import topology.metric_space.emetric_paracompact

import to_mathlib.topology.nhds_set

open set filter
open_locale manifold topological_space

lemma exists_cont_diff_zero_one {E : Type*} [normed_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ eq_on f 0 s ∧ eq_on f 1 t ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_of_closed 𝓘(ℝ, E) hs ht hd
in ⟨f, f.smooth.cont_diff, hfs, hft, hf01⟩

lemma exists_cont_diff_zero_one_nhds {E : Type*} [normed_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  rcases normal_exists_closure_subset hs ht.is_open_compl (disjoint_iff_subset_compl_left.mp hd.symm) with ⟨u, u_op, hsu, hut⟩,
  have hcu : is_closed (closure u) := is_closed_closure,
  rcases normal_exists_closure_subset ht hcu.is_open_compl (subset_compl_comm.mp hut) with ⟨v, v_op, htv, hvu⟩,
  have hcv : is_closed (closure v) := is_closed_closure,
  rcases exists_cont_diff_zero_one hcu hcv (disjoint_iff_subset_compl_left.mpr hvu) with ⟨f, hfsmooth, hfu, hfv, hf⟩,
  refine ⟨f, hfsmooth, _, _, hf⟩,
  apply eventually_of_mem (mem_of_superset (u_op.mem_nhds_set.mpr hsu) subset_closure) hfu,
  apply eventually_of_mem (mem_of_superset (v_op.mem_nhds_set.mpr htv) subset_closure) hfv
end

lemma exists_cont_diff_one_nhds_of_interior {E : Type*} [normed_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (hd : s ⊆ interior t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : is_closed (interior t)ᶜ,
  exact is_open_interior.is_closed_compl,

  rcases exists_cont_diff_zero_one_nhds this hs _ with ⟨f, hfsmooth, h0, h1, hf⟩,
  { refine ⟨f, hfsmooth, h1, _, hf⟩,
    intros x hx,
    exact h0.on_set _ (λ hx', hx $ interior_subset hx') },
  rwa [disjoint_iff_subset_compl_left, compl_compl]
end


section zulip

open_locale topological_space filter big_operators
open set function filter

variables
  {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]


lemma partition_induction_on
  {P : E → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : with_top ℕ}
  (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff ℝ n f ∧ ∀ x, P x (f x) :=
begin
  choose U hU hU' using hP',
  choose φ hφ using hU',
  rcases smooth_bump_covering.exists_is_subordinate 𝓘(ℝ, E) is_closed_univ (λ x h, hU x) with
    ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  have sum_ρ := λ x, ρ.sum_eq_one (mem_univ x),
  have nonneg_ρ := ρ.nonneg,
  have lf : locally_finite (λ (i : ι), support (λ x, ρ i x • φ (b.c i) x)),
  { refine ρ.locally_finite.subset (λ i x hx hx', hx _),
    dsimp only,
    rw [hx', zero_smul] },
  refine ⟨λ x : E, (∑ᶠ i, (ρ i x) • φ (b.c i) x), cont_diff_iff_cont_diff_at.mpr _, _⟩,
  all_goals {
    intros x,
    rcases lf x with ⟨V, V_in : V ∈ 𝓝 x,
                      hV : {i : ι | (support (λ x, ρ i x • φ (b.c i) x) ∩ V).nonempty}.finite⟩},
  { sorry },
  { have := λ i, (hφ $ b.c i).2,
    sorry },
end

lemma convex_set_of_imp_eq (P : Prop) (y : F) : convex ℝ {x : F | P → x = y } :=
by by_cases hP : P; simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eq_on_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

-- lemma exists_smooth_and_eq_on_aux2 {n : with_top ℕ} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

lemma exists_smooth_and_eq_on {n : with_top ℕ} {f : E → F} {ε : E → ℝ} (hf : continuous f)
  (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
  {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U) :
  ∃ f' : E → F, cont_diff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ eq_on f' f s :=
begin
  have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
  let P : E → F → Prop := λ x t, dist t (f x) < ε x ∧ (x ∈ s → t = f x),
  have hP : ∀ x, convex ℝ {y | P x y} :=
    λ x, (convex_ball (f x) (ε x)).inter (convex_set_of_imp_eq _ _),
  obtain ⟨f', hf', hPf'⟩ := partition_induction_on hP _,
  { exact ⟨f', hf', λ x, (hPf' x).1, λ x, (hPf' x).2⟩ },
  { intros x,
    obtain ⟨U, hU, hfU⟩ := hfs,
    by_cases hx : x ∈ s,
    { refine ⟨U, mem_nhds_set_iff_forall.mp hU x hx, _⟩,
      refine ⟨f, hfU, λ y _, ⟨h0 y, λ _, rfl⟩⟩ },
    { have : is_open {y : E | dist (f x) (f y) < ε y} := is_open_lt (continuous_const.dist hf) hε,
      exact ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, λ _, f x, cont_diff_on_const,
        λ y hy, ⟨hy.1, λ h2y, (hy.2 h2y).elim⟩⟩ } },
end

end zulip
