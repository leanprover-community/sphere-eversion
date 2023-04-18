import to_mathlib.geometry.manifold.misc_manifold

open bundle set function filter
open_locale manifold topology
noncomputable theory

section topology

variables {α β γ : Type*} [topological_space α] [topological_space β]

lemma map_fst_nhds_within_eq {x : α × β} {s : set α} :
  map prod.fst (𝓝[prod.fst ⁻¹' s] x) = 𝓝[s] x.1 :=
by { cases x, rw [← prod_univ, nhds_within_prod_eq, nhds_within_univ, map_fst_prod] }

lemma nhds_within_preimage_fst_le {x : α × β} {s : set α} :
  𝓝[prod.fst ⁻¹' s] x ≤ comap prod.fst (𝓝[s] x.1) :=
by { rw [← map_fst_nhds_within_eq], exact le_comap_map }

lemma filter.eventually.nhds_within_preimage_fst {z : α × β} {s : set α} {p : α × β → Prop}
  (h : ∀ᶠ x in 𝓝[s] z.1, ∀ y, p (x, y)) : ∀ᶠ z' in 𝓝[prod.fst ⁻¹' s] z, p z' :=
begin
  refine eventually.filter_mono nhds_within_preimage_fst_le _,
  simp_rw [eventually_comap, prod.forall],
  simp only [forall_swap] {single_pass := tt},
  convert h, ext x,
  refine forall_congr (λ y, _),
  simp_rw [forall_eq],
end

lemma filter.eventually_eq.nhds_within_preimage_fst {z : α × β} {s : set α} {f g : α × β → γ}
  (h : curry f =ᶠ[𝓝[s] z.1] curry g) : f =ᶠ[𝓝[prod.fst ⁻¹' s] z] g :=
filter.eventually.nhds_within_preimage_fst $ by { simp_rw [← funext_iff], exact h }

lemma eventually_mem_nhds_within' {α} [topological_space α] {s t : set α} {a : α} :
  (∀ᶠ x in 𝓝[s] a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
eventually_nhds_within_nhds_within

lemma eventually_mem_nhds_within'' {α} [topological_space α] {s t : set α} {a : α} :
  (∀ᶠ x in 𝓝 a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
eventually_nhds_nhds_within

end topology

section vector_bundle

open smooth_manifold_with_corners
open_locale bundle

variables {𝕜 B F M : Type*} {E : B → Type*}
  [nontrivially_normed_field 𝕜]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] {IB : model_with_corners 𝕜 EB HB}
  [topological_space B] [charted_space HB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M]
  {n : ℕ∞}
  [fiber_bundle F E] [vector_bundle 𝕜 F E]
  {e e' : trivialization F (π E)}

variables (IB) [smooth_manifold_with_corners IB B] [smooth_vector_bundle F E IB]

theorem trivialization.smooth_at (e : trivialization F (π E)) [mem_trivialization_atlas e]
  {x₀ : total_space E} (hx₀ : x₀.proj ∈ e.base_set) :
  smooth_at (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e x₀ :=
begin
  rw [smooth_at_prod],
  refine ⟨(smooth_at_proj E).congr_of_eventually_eq _, _⟩,
  { exact eventually_of_mem (e.open_source.mem_nhds $ e.mem_source.mpr hx₀)
      (λ x hx, e.coe_fst hx) },
  simp_rw [smooth_at, cont_mdiff_at_iff_source_of_mem_source (mem_chart_source _ _)],
  simp only [fiber_bundle.ext_chart_at, function.comp, prod_univ, -ext_chart_at] with mfld_simps,
  let e' := trivialization_at F E x₀.proj,
  let c := (ext_chart_at IB x₀.proj).symm,
  have h0 := (ext_chart_at IB x₀.proj).left_inv (mem_ext_chart_source IB x₀.proj),
  have : cont_mdiff_within_at 𝓘(𝕜, EB × F) 𝓘(𝕜, F) ⊤
    (λ (x : EB × F), e'.coord_changeL 𝕜 e (c x.1) x.2)
    (prod.fst ⁻¹' range IB) (ext_chart_at IB x₀.proj x₀.proj, (e' x₀).2),
  { refine cont_mdiff_within_at.clm_apply _ cont_diff_within_at_snd.cont_mdiff_within_at,
    have h1 := smooth_at_coord_change IB e' e ⟨mem_base_set_trivialization_at F E x₀.proj, hx₀⟩,
    refine h1.cont_mdiff_within_at.comp_of_eq _ (maps_to_univ _ _) _,
    { refine ((cont_mdiff_on_ext_chart_at_symm IB x₀.proj _ $ (ext_chart_at IB x₀.proj).maps_to $
        mem_ext_chart_source IB x₀.proj).mono_of_mem _).comp_of_eq _ (maps_to_preimage _ _) rfl,
      { exact ext_chart_at_target_mem_nhds_within IB x₀.proj },
      exact cont_diff_within_at_fst.cont_mdiff_within_at },
    exact h0 },
  refine this.congr_of_eventually_eq_insert _,
  rw [insert_eq_of_mem],
  swap, exact mem_range_self _,
  refine filter.eventually.nhds_within_preimage_fst _,
  dsimp only,
  have h1 := (continuous_at_ext_chart_at_symm IB x₀.proj).preimage_mem_nhds
    ((trivialization_at F E _).open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  rw [h0] at h1,
  have h2 := (continuous_at_ext_chart_at_symm IB x₀.proj).preimage_mem_nhds
    (e.open_base_set.mem_nhds $ by rwa [h0]),
  filter_upwards [nhds_within_le_nhds h1, nhds_within_le_nhds h2] with b h1b h2b y,
  rw [e'.coord_changeL_apply e ⟨h1b, h2b⟩, e'.mk_symm h1b]
end

theorem trivialization.smooth_on (e : trivialization F (π E)) [mem_trivialization_atlas e] :
  smooth_on (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e e.source :=
λ x hx, (e.smooth_at IB $ e.mem_source.mp hx).smooth_within_at

theorem smooth_at_trivialization_at
  {x₀ : B} {x : total_space E} (hx : x.proj ∈ (trivialization_at F E x₀).base_set) :
  smooth_at (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivialization_at F E x₀) x :=
(trivialization_at F E x₀).smooth_at IB hx

theorem smooth_on_trivialization_at (x₀ : B) :
  smooth_on (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivialization_at F E x₀)
  (trivialization_at F E x₀).source :=
(trivialization_at F E x₀).smooth_on IB

end vector_bundle


section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {N' : Type*} [topological_space N'] [charted_space G' N']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x' : M}
-- declare some additional normed spaces, used for fibers of vector bundles
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

-- lemma cont_mdiff_within_at_insert :
--   cont_mdiff_within_at I I' n f (insert x' s) x ↔ cont_mdiff_within_at I I' n f s x :=
-- begin
--   sorry
-- end

-- alias cont_mdiff_within_at_insert ↔ cont_mdiff_within_at.of_insert cont_mdiff_within_at.insert'

-- lemma cont_mdiff_within_at.insert (h : cont_mdiff_within_at I I' n f s x) :
--   cont_mdiff_within_at I I' n f (insert x s) x :=
-- h.insert'

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma cont_mdiff_within_at_iff_cont_mdiff_within_at_nhds_within {n : ℕ} :
  cont_mdiff_within_at I I' n f s x ↔
  ∀ᶠ x' in 𝓝[insert x s] x, cont_mdiff_within_at I I' n f s x' :=
begin
  refine ⟨_, λ h, h.self_of_nhds_within (mem_insert x s)⟩,
  rw [cont_mdiff_within_at_iff_cont_mdiff_on_nhds],
  rintro ⟨u, hu, h⟩,
  filter_upwards [eventually_mem_nhds_within'.mpr hu, hu] with x' hx' h2x',
  exact (h x' h2x').mono_of_mem (nhds_within_mono x' (subset_insert x s) hx')
end


open bundle
variables
  {Z : M → Type*} [topological_space (total_space Z)] [∀ b, topological_space (Z b)]
  [∀ b, add_comm_monoid (Z b)] [∀ b, module 𝕜 (Z b)]
  [fiber_bundle F₁ Z] [vector_bundle 𝕜 F₁ Z] [smooth_vector_bundle F₁ Z I]
  {Z₂ : M' → Type*} [topological_space (total_space Z₂)] [∀ b, topological_space (Z₂ b)]
  [∀ b, add_comm_monoid (Z₂ b)] [∀ b, module 𝕜 (Z₂ b)]
  [fiber_bundle F₂ Z₂] [vector_bundle 𝕜 F₂ Z₂] [smooth_vector_bundle F₂ Z₂ I']

open_locale bundle

variables (I I' Z Z₂ F₁ F₂)

variables {I I'}

attribute [mfld_simps] mem_insert_iff

-- /-- Proving this without the assumption `x₀ ∈ s` might be possible, but is nontrivial.
--   Todo: use `mfderiv_within`, either with the same set or a different set. -/
-- lemma cont_mdiff_within_at.mfderiv {s : set N} {x₀ : N} (f : N → M → M') (g : N → M)
--   (hf : cont_mdiff_within_at (J.prod I) I' n (function.uncurry f) (prod.fst ⁻¹' s) (x₀, g x₀))
--   (hg : cont_mdiff_within_at J I m g s x₀) (hx₀ : x₀ ∈ s) (hmn : m + 1 ≤ n) :
--   cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) s x₀ :=
-- begin
--   have h4f : (λ x, f x (g x)) ⁻¹' (ext_chart_at I' (f x₀ (g x₀))).source ∈ 𝓝[s] x₀,
--   { have : continuous_within_at (λ x, f x (g x)) s x₀,
--     { apply continuous_within_at.comp (by apply hf.continuous_within_at)
--         (continuous_within_at_id.prod hg.continuous_within_at),
--       simp_rw [maps_to', image_subset_iff, preimage_preimage, preimage_id] },
--     exact this.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds I' (f x₀ (g x₀))) },
--   have h2f : ∀ᶠ x₂ in 𝓝[s] x₀, cont_mdiff_within_at I I' 1 (f x₂) (g '' s) (g x₂),
--   { have := cont_mdiff_within_at_iff_cont_mdiff_within_at_nhds_within.mp
--       (hf.of_le $ (self_le_add_left 1 m).trans hmn),
--     have := (continuous_within_at_id.prod hg.continuous_within_at).eventually _,
--     filter_upwards [this] with x hx,
--     swap, exact cont_mdiff_within_at (J.prod I) I' ↑1 (uncurry f) (prod.fst ⁻¹' s),
--     refine hx.comp (g x) (cont_mdiff_within_at_const.prod_mk cont_mdiff_within_at_id) _,
--     classical,
--     simp_rw [maps_to', image_subset_iff, preimage_preimage, id, preimage_const],
--     sorry, --false
--     sorry
--     },
--   have h2g : g ⁻¹' (ext_chart_at I (g x₀)).source ∈ 𝓝[s] x₀ :=
--     hg.continuous_within_at.preimage_mem_nhds_within
--       (ext_chart_at_source_mem_nhds I (g x₀)),
--   have : cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜
--     (ext_chart_at I' (f x₀ (g x₀)) ∘ f ((ext_chart_at J x₀).symm x') ∘ (ext_chart_at I (g x₀)).symm)
--     (range I) (ext_chart_at I (g x₀) (g ((ext_chart_at J x₀).symm x'))))
--     ((ext_chart_at J x₀).symm ⁻¹' s ∩ range J) (ext_chart_at J x₀ x₀),
--   { rw [cont_mdiff_within_at_iff] at hf hg,
--     simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
--     refine (cont_diff_within_at_fderiv_within _
--       (hg.2.insert.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
--     swap 3,
--     { simp_rw [function.comp, ext_chart_at_to_inv], exact hf.2.insert },
--     { refine (ext_chart_at J x₀).symm ⁻¹' (s) ∩ (ext_chart_at J x₀).target ∩
--         (ext_chart_at J x₀).symm ⁻¹' (g ⁻¹' (ext_chart_at I (g x₀)).source) },
--     { refine mem_of_superset self_mem_nhds_within ((inter_subset_left _ _).trans $ _),
--       sorry -- set theory made stupid because of an insert
--       -- exact inter_subset_inter_right _ (ext_chart_at_target_subset_range J x₀)
--       },
--     { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
--       exact ⟨⟨hx₀, local_equiv.maps_to _ (mem_ext_chart_source J x₀)⟩,
--         mem_ext_chart_source I (g x₀)⟩ },
--     { simp_rw [model_with_corners.range_prod],
--       rw [inter_assoc, inter_prod],
--       sorry,  -- more stupid set theory made stupid because of an insert
--       -- refine inter_subset_inter _ _,
--       -- { sorry },
--       -- exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x₀)
--       --   subset_rfl
--          },
--     { refine eventually_of_forall (λ x', mem_range_self _) },
--     swap 2,
--     { sorry,
--       -- refine inter_mem (ext_chart_at_target_mem_nhds_within J x₀) _,
--       -- ext_chart_at_preimage_mem_nhds_within
--       -- refine nhds_within_le_nhds (ext_chart_at_preimage_mem_nhds' _ _ (mem_ext_chart_source J x₀) _),
--       -- exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀))
--       },
--     simp_rw [function.comp, ext_chart_at_to_inv],
--     refine mem_of_superset self_mem_nhds_within _,
--     refine (image_subset_range _ _).trans _,
--     exact range_comp_subset_range (λ a, chart_at H (g x₀) $ g $ (chart_at G x₀).symm $ J.symm a) I },
--   have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ f x' ∘ (ext_chart_at I (g x₀)).symm)
--     (range I) (ext_chart_at I (g x₀) (g x'))) s x₀,
--   { simp_rw [cont_mdiff_within_at_iff_source_of_mem_source (mem_chart_source G x₀),
--       cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
--     exact this },
--   have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x' (g x'))).symm ∘
--       written_in_ext_chart_at I I' (g x') (f x') ∘ ext_chart_at I (g x') ∘
--       (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x'))) s x₀,
--   { refine this.congr_of_eventually_eq_insert _,
--     rw [insert_eq_of_mem hx₀],
--     filter_upwards [h2g, h2f],
--     intros x₂ hx₂ h2x₂,
--     have : ∀ x' ∈ (ext_chart_at I (g x₀)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
--         (ext_chart_at I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
--       (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
--       written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
--       (ext_chart_at I (g x₀)).symm) x' =
--       ext_chart_at I' (f x₀ (g x₀)) (f x₂ ((ext_chart_at I (g x₀)).symm x')),
--     { rintro x' ⟨hx', h2x'⟩,
--       simp_rw [written_in_ext_chart_at, function.comp_apply],
--       rw [(ext_chart_at I (g x₂)).left_inv hx', (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x'] },
--     refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
--     refine eventually_of_mem (inter_mem _ _) this,
--     { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
--     refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
--     sorry
--     -- exact h2x₂.continuous_within_at.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _)
--      },
--   refine this.congr_of_eventually_eq_insert _,
--   rw [insert_eq_of_mem hx₀],
--   filter_upwards [h2g, h2f, h4f],
--   intros x₂ hx₂ h2x₂ h3x₂,
--   symmetry,
--   rw [in_tangent_coordinates_core_eq],
--   swap, { rwa [ext_chart_at_source] at hx₂ },
--   swap, { rwa [ext_chart_at_source] at h3x₂ },
--   sorry,
--   -- rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
--   -- have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x₀) $
--   --   local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
--   --   .differentiable_within_at le_top,
--   -- have hI' := (cont_diff_within_at_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
--   --   local_equiv.mem_symm_trans_source _
--   --   (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
--   -- have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
--   -- refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
--   -- { exact λ x _, mem_range_self _ },
--   -- { exact λ x _, mem_range_self _ },
--   -- { simp_rw [written_in_ext_chart_at, function.comp_apply,
--   --     (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
--   -- { simp_rw [function.comp_apply, (ext_chart_at I (g x₀)).left_inv hx₂] }
-- end

-- lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
--   (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
--   (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
--   cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
-- begin
--   sorry
-- end

theorem cont_mdiff_at_tangent_bundle_trivialization_at_continuous_linear_map
  (x₀ : tangent_bundle I M) :
  cont_mdiff_at I.tangent 𝓘(𝕜, E) m (λ x : tangent_bundle I M,
    (trivialization_at E (tangent_space I) x₀.proj).continuous_linear_map_at 𝕜 x.proj x.2) x₀ :=
begin
  let e := trivialization_at E (tangent_space I) x₀.proj,
  refine cont_mdiff_at.congr_of_eventually_eq _ _,
  swap 3,
  have h1 := (continuous_proj E (tangent_space I)).continuous_at.preimage_mem_nhds
    (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  filter_upwards [h1] with x hx,
  rw [trivialization.continuous_linear_map_at_apply, e.coe_linear_map_at_of_mem hx],
  exact (e.smooth_at I $ mem_base_set_trivialization_at E _ _).snd.of_le le_top,
end

/-- Not useful by itself. TODO: generalize to `cont_mdiff_within_at` of `tangent_map_within` -/
theorem cont_mdiff_at.cont_mdiff_at_tangent_map (x₀ : tangent_bundle I M)
  (hf : cont_mdiff_at I I' n f x₀.proj) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I.tangent I'.tangent m (tangent_map I I' f) x₀ :=
begin
  rw cont_mdiff_at_total_space,
  refine ⟨(hf.comp x₀ (cont_mdiff_at_proj (tangent_space I))).of_le $
    (self_le_add_right m 1).trans hmn, _⟩,
  dsimp only [tangent_map, total_space.proj_mk],
  let e := trivialization_at E (tangent_space I) x₀.proj,
  let e' := trivialization_at E' (tangent_space I') (f x₀.proj),
  have : cont_mdiff_at I.tangent 𝓘(𝕜, E') m (λ x : tangent_bundle I M,
    in_tangent_coordinates I I' id f (mfderiv I I' f) x₀.proj x.proj $
    e.continuous_linear_map_at 𝕜 x.proj x.2) x₀,
  { refine cont_mdiff_at.mfderiv_apply (λ _, f) id total_space.proj
      (λ x, e.continuous_linear_map_at 𝕜 x.proj x.2) _ cont_mdiff_at_id (cont_mdiff_at_proj _) _
      hmn,
    apply cont_mdiff_at.comp (x₀.proj, x₀.proj) (by exact hf) cont_mdiff_at_snd,
    apply cont_mdiff_at_tangent_bundle_trivialization_at_continuous_linear_map },
  refine this.congr_of_eventually_eq _,
  have h1 := (continuous_proj E (tangent_space I)).continuous_at.preimage_mem_nhds
    (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  have h2 := (hf.continuous_at.comp (continuous_proj E (tangent_space I)).continuous_at)
    .preimage_mem_nhds (e'.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  filter_upwards [h1, h2] with x hx h2x,
  dsimp only [in_tangent_coordinates, in_coordinates, id_def],
  simp_rw [continuous_linear_map.comp_apply, e.symmL_continuous_linear_map_at hx,
    trivialization.continuous_linear_map_at_apply, e'.coe_linear_map_at_of_mem h2x],
end

end smooth_manifold_with_corners
