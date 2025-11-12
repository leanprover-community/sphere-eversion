import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Bundle Set Function Filter ContinuousLinearMap

open scoped Manifold Topology

noncomputable section

open Function
section Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem map_fst_nhdsWithin_eq {x : α × β} {s : Set α} :
    map Prod.fst (𝓝[Prod.fst ⁻¹' s] x) = 𝓝[s] x.1 := by
  cases x
  rw [← prod_univ, nhdsWithin_prod_eq, nhdsWithin_univ, map_fst_prod]

theorem nhdsWithin_preimage_fst_le {x : α × β} {s : Set α} :
    𝓝[Prod.fst ⁻¹' s] x ≤ comap Prod.fst (𝓝[s] x.1) := by
  rw [← map_fst_nhdsWithin_eq]
  exact le_comap_map

theorem Filter.Eventually.nhdsWithin_preimage_fst {z : α × β} {s : Set α} {p : α × β → Prop}
    (h : ∀ᶠ x in 𝓝[s] z.1, ∀ y, p (x, y)) : ∀ᶠ z' in 𝓝[Prod.fst ⁻¹' s] z, p z' := by
  rw [← map_fst_nhdsWithin_eq, eventually_map] at h
  exact h.mono fun z hz ↦ hz _

theorem Filter.EventuallyEq.nhdsWithin_preimage_fst {z : α × β} {s : Set α} {f g : α × β → γ}
    (h : f.curry =ᶠ[𝓝[s] z.1] g.curry) : f =ᶠ[𝓝[Prod.fst ⁻¹' s] z] g :=
  Filter.Eventually.nhdsWithin_preimage_fst <| by simp_rw [← funext_iff]; exact h

theorem eventually_mem_nhds_within' {α} [TopologicalSpace α] {s t : Set α} {a : α} :
    (∀ᶠ x in 𝓝[s] a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
  eventually_eventually_nhdsWithin

theorem eventually_mem_nhds_within'' {α} [TopologicalSpace α] {s t : Set α} {a : α} :
    (∀ᶠ x in 𝓝 a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
  eventually_nhds_nhdsWithin

end Topology

section VectorBundle

open IsManifold VectorBundleCore

open scoped Bundle ContDiff

variable {𝕜 B F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞} [FiberBundle F E] [VectorBundle 𝕜 F E]
  {e e' : Trivialization F (π F E)}

theorem VectorBundleCore.smoothAt_coordChange {ι} (Z : VectorBundleCore 𝕜 B F ι) [Z.IsContMDiff IB ∞]
    (i j : ι) {x₀ : B} (hx₀ : x₀ ∈ Z.baseSet i ∩ Z.baseSet j) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) ∞ (Z.coordChange i j) x₀ :=
  (Z.contMDiffOn_coordChange IB i j).contMDiffAt <|
    ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).mem_nhds hx₀

variable (IB)
variable [ContMDiffVectorBundle ∞ F E IB]

theorem smoothAt_coord_change (e e' : Trivialization F (π F E)) {x₀ : B}
    (hx₀ : x₀ ∈ e.baseSet ∩ e'.baseSet) [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) ∞ (fun b : B ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x₀ :=
  (contMDiffOn_coordChangeL e e').contMDiffAt <| (e.open_baseSet.inter e'.open_baseSet).mem_nhds hx₀

variable {IB}

theorem contMDiffAt_coord_change_apply (e e' : Trivialization F (π F E)) {x₀ : M} {f : M → B}
    {g : M → F} (hf : ContMDiffAt IM IB n f x₀) (hg : ContMDiffAt IM 𝓘(𝕜, F) n g x₀)
    (hx₀ : f x₀ ∈ e.baseSet ∩ e'.baseSet) [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ e.coordChangeL 𝕜 e' (f x) (g x)) x₀ :=
  (((smoothAt_coord_change IB e e' hx₀).of_le sorry).comp x₀ hf).clm_apply hg

end VectorBundle

section VectorBundle

open IsManifold

open scoped Bundle ContDiff

variable {𝕜 B F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞} [FiberBundle F E] [VectorBundle 𝕜 F E] {e e' : Trivialization F (π F E)}

variable (IB)
variable [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F E IB]

-- TODO: rename to contMDiffAt
theorem Trivialization.smoothAt (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {x₀ : TotalSpace F E} (hx₀ : x₀.proj ∈ e.baseSet) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ∞ e x₀ := by
  rw [@contMDiffAt_prod_iff]
  refine ⟨(contMDiffAt_proj E).congr_of_eventuallyEq ?_, ?_⟩
  · exact eventually_of_mem (e.open_source.mem_nhds <| e.mem_source.mpr hx₀) fun x hx ↦ e.coe_fst hx
  simp_rw [contMDiffAt_iff_source_of_mem_source (mem_chart_source _ _)]
  simp only [FiberBundle.extChartAt, Function.comp, prod_univ, mfld_simps]
  let e' := trivializationAt F E x₀.proj
  let c := (extChartAt IB x₀.proj).symm
  have h0 := (extChartAt IB x₀.proj).left_inv (mem_extChartAt_source x₀.proj)
  have : ContMDiffWithinAt 𝓘(𝕜, EB × F) 𝓘(𝕜, F) ∞
      (fun x : EB × F ↦ e'.coordChangeL 𝕜 e (c x.1) x.2)
      (Prod.fst ⁻¹' range IB) (extChartAt IB x₀.proj x₀.proj, (e' x₀).2) := by
    sorry /-refine ContMDiffWithinAt.clm_apply (𝕜 := 𝕜) ?_ contDiffWithinAt_snd.contMDiffWithinAt
    have h1 := smoothAt_coord_change IB e' e ⟨mem_base_set_trivialization_at F E x₀.proj, hx₀⟩
    refine' h1.cont_mdiff_within_at.comp_of_eq _ (maps_to_univ _ _) _
    · refine' ((contMDiffOn_extChartAt_symm x₀.proj _ <|
          (extChartAt IB x₀.proj).mapsTo <| mem_extChartAt_source IB x₀.proj).mono_of_mem
        _).comp_of_eq _ (mapsTo_preimage _ _) rfl
      · exact extChartAt_target_mem_nhdsWithin IB x₀.proj
      exact contDiffWithinAt_fst.contMDiffWithinAt
    · exact h0 -/
  sorry /- was: refine this.congr_of_eventuallyEq_insert ?_
  rw [insert_eq_of_mem]
  swap; exact mem_range_self _
  refine' Filter.Eventually.nhdsWithin_preimage_fst _
  dsimp only
  have h1 :=
    (continuousAt_extChartAt_symm IB x₀.proj).preimage_mem_nhds
      ((trivialization_at F E _).open_baseSet.mem_nhds <| mem_base_set_trivialization_at _ _ _)
  rw [h0] at h1
  have h2 :=
    (continuousAt_extChartAt_symm IB x₀.proj).preimage_mem_nhds
      (e.open_base_set.mem_nhds <| by rwa [h0])
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with b h1b h2b y
  rw [e'.coord_changeL_apply e ⟨h1b, h2b⟩, e'.mk_symm h1b] -/

#print Trivialization.contMDiffOn /-
theorem Trivialization.smoothOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    SmoothOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e e.source := fun x hx ↦
  (e.smoothAt IB <| e.mem_source.mp hx).smoothWithinAt
-/

theorem smoothAt_trivializationAt {x₀ : B} {x : TotalSpace F E}
    (hx : x.proj ∈ (trivializationAt F E x₀).baseSet) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ∞ (trivializationAt F E x₀) x :=
  (trivializationAt F E x₀).smoothAt IB hx

omit [IsManifold IB ∞ B] in
theorem smoothOn_trivializationAt (x₀ : B) :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ∞ (trivializationAt F E x₀)
      (trivializationAt F E x₀).source :=
  (trivializationAt F E x₀).contMDiffOn

end VectorBundle

section SmoothManifoldWithCorners

open IsManifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*} [TopologicalSpace N']
  [ChartedSpace G' N'] {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']

variable {f : M → M'} {m n : ℕ∞} {s : Set M} {x x' : M}
  -- declare some additional normed spaces, used for fibers of vector bundles
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂]

variable [IsManifold I ∞ M] [IsManifold I' ∞ M']
  [IsManifold J ∞ N]

-- lemma cont_mdiff_within_at_insert :
--   cont_mdiff_within_at I I' n f (insert x' s) x ↔ cont_mdiff_within_at I I' n f s x :=
-- begin
--   sorry
-- end
-- alias cont_mdiff_within_at_insert ↔ cont_mdiff_within_at.of_insert cont_mdiff_within_at.insert'
-- lemma cont_mdiff_within_at.insert (h : cont_mdiff_within_at I I' n f s x) :
--   cont_mdiff_within_at I I' n f (insert x s) x :=
-- h.insert'

open Bundle

variable {Z : M → Type*} [TopologicalSpace (TotalSpace F₁ Z)] [∀ b, TopologicalSpace (Z b)]
  [∀ b, AddCommMonoid (Z b)] [∀ b, Module 𝕜 (Z b)] [FiberBundle F₁ Z] [VectorBundle 𝕜 F₁ Z]
  [ContMDiffVectorBundle ∞ F₁ Z I] {Z₂ : M' → Type*} [TopologicalSpace (TotalSpace F₂ Z₂)]
  [∀ b, TopologicalSpace (Z₂ b)] [∀ b, AddCommMonoid (Z₂ b)] [∀ b, Module 𝕜 (Z₂ b)]
  [FiberBundle F₂ Z₂] [VectorBundle 𝕜 F₂ Z₂] [ContMDiffVectorBundle ∞ F₂ Z₂ I']

open scoped Bundle

variable (I I' Z Z₂ F₁ F₂)

variable {I I'}

attribute [mfld_simps] mem_insert_iff

-- /-- Proving this without the assumption `x₀ ∈ s` might be possible, but is nontrivial.
--   Todo: use `mfderiv_within`, either with the same set or a different set. -/
-- lemma cont_mdiff_within_at.mfderiv {s : set N} {x₀ : N} (f : N → M → M') (g : N → M)
--   (hf : cont_mdiff_within_at (J.prod I) I' n (function.uncurry f) (prod.fst ⁻¹' s) (x₀, g x₀))
--   (hg : cont_mdiff_within_at J I m g s x₀) (hx₀ : x₀ ∈ s) (hmn : m + 1 ≤ n) :
--   cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) s x₀ :=
-- begin
--   have h4f : (λ x, f x (g x)) ⁻¹' (extChartAt I' (f x₀ (g x₀))).source ∈ 𝓝[s] x₀,
--   { have : continuous_within_at (λ x, f x (g x)) s x₀,
--     { apply continuous_within_at.comp (by apply hf.continuous_within_at)
--         (continuous_within_at_id.prod hg.continuous_within_at),
--       simp_rw [maps_to', image_subset_iff, preimage_preimage, preimage_id] },
--     exact this.preimage_mem_nhds_within (extChartAt_source_mem_nhds I' (f x₀ (g x₀))) },
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
--   have h2g : g ⁻¹' (extChartAt I (g x₀)).source ∈ 𝓝[s] x₀ :=
--     hg.continuous_within_at.preimage_mem_nhds_within
--       (extChartAt_source_mem_nhds I (g x₀)),
--   have : contDiffWithinAt 𝕜 m (λ x', fderivWithin 𝕜
--     (extChartAt I' (f x₀ (g x₀)) ∘ f ((extChartAt J x₀).symm x') ∘ (extChartAt I (g x₀)).symm)
--     (range I) (extChartAt I (g x₀) (g ((extChartAt J x₀).symm x'))))
--     ((extChartAt J x₀).symm ⁻¹' s ∩ range J) (extChartAt J x₀ x₀),
--   { rw [cont_mdiff_within_at_iff] at hf hg,
--     simp_rw [function.comp, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm] at hf ⊢,
--     refine (contDiffWithinAt_fderivWithin _
--       (hg.2.insert.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
--     swap 3,
--     { simp_rw [function.comp, extChartAt_to_inv], exact hf.2.insert },
--     { refine (extChartAt J x₀).symm ⁻¹' (s) ∩ (extChartAt J x₀).target ∩
--         (extChartAt J x₀).symm ⁻¹' (g ⁻¹' (extChartAt I (g x₀)).source) },
--     { refine mem_of_superset self_mem_nhds_within ((inter_subset_left _ _).trans $ _),
--       sorry -- set theory made stupid because of an insert
--       -- exact inter_subset_inter_right _ (extChartAt_target_subset_range J x₀)
--       },
--     { simp_rw [mem_inter_iff, mem_preimage, extChartAt_to_inv],
--       exact ⟨⟨hx₀, PartialEquiv.maps_to _ (mem_ext_chart_source J x₀)⟩,
--         mem_ext_chart_source I (g x₀)⟩ },
--     { simp_rw [model_with_corners.range_prod],
--       rw [inter_assoc, inter_prod],
--       sorry,  -- more stupid set theory made stupid because of an insert
--       -- refine inter_subset_inter _ _,
--       -- { sorry },
--       -- exact set.prod_mono ((inter_subset_left _ _).trans $ extChartAt_target_subset_range J x₀)
--       --   Subset.rfl
--          },
--     { refine eventually_of_forall (λ x', mem_range_self _) },
--     swap 2,
--     { sorry,
--       -- refine inter_mem (extChartAt_target_mem_nhds_within J x₀) _,
--       -- extChartAt_preimage_mem_nhds_within
--       -- refine nhds_within_le_nhds (extChartAt_preimage_mem_nhds' _ _ (mem_ext_chart_source J x₀) _),
--       -- exact hg.1.preimage_mem_nhds (extChartAt_source_mem_nhds I (g x₀))
--       },
--     simp_rw [function.comp, extChartAt_to_inv],
--     refine mem_of_superset self_mem_nhds_within _,
--     refine (image_subset_range _ _).trans _,
--     exact range_comp_subset_range (λ a, chartAt H (g x₀) $ g $ (chartAt G x₀).symm $ J.symm a) I },
--   have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (λ x', fderiv_within 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ f x' ∘ (extChartAt I (g x₀)).symm)
--     (range I) (extChartAt I (g x₀) (g x'))) s x₀,
--   { simp_rw [cont_mdiff_within_at_iff_source_of_mem_source (mem_chart_source G x₀),
--       contMDiffWithinAt_iff_contDiffWithinAt, function.comp],
--     exact this },
--   have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (λ x', fderiv_within 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ (extChartAt I' (f x' (g x'))).symm ∘
--       written_in_extChartAt I I' (g x') (f x') ∘ extChartAt I (g x') ∘
--       (extChartAt I (g x₀)).symm) (range I) (extChartAt I (g x₀) (g x'))) s x₀,
--   { refine this.congr_of_eventually_eq_insert _,
--     rw [insert_eq_of_mem hx₀],
--     filter_upwards [h2g, h2f],
--     intros x₂ hx₂ h2x₂,
--     have : ∀ x' ∈ (extChartAt I (g x₀)).symm ⁻¹' (extChartAt I (g x₂)).source ∩
--         (extChartAt I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (extChartAt I' (f x₂ (g x₂))).source),
--       (extChartAt I' (f x₀ (g x₀)) ∘ (extChartAt I' (f x₂ (g x₂))).symm ∘
--       written_in_extChartAt I I' (g x₂) (f x₂) ∘ extChartAt I (g x₂) ∘
--       (extChartAt I (g x₀)).symm) x' =
--       extChartAt I' (f x₀ (g x₀)) (f x₂ ((extChartAt I (g x₀)).symm x')),
--     { rintro x' ⟨hx', h2x'⟩,
--       simp_rw [written_in_extChartAt, function.comp_apply],
--       rw [(extChartAt I (g x₂)).left_inv hx', (extChartAt I' (f x₂ (g x₂))).left_inv h2x'] },
--     refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
--     refine eventually_of_mem (inter_mem _ _) this,
--     { exact extChartAt_preimage_mem_nhds' _ _ hx₂ (extChartAt_source_mem_nhds I (g x₂)) },
--     refine extChartAt_preimage_mem_nhds' _ _ hx₂ _,
--     sorry
--     -- exact h2x₂.continuous_within_at.preimage_mem_nhds_within (extChartAt_source_mem_nhds _ _)
--      },
--   refine this.congr_of_eventually_eq_insert _,
--   rw [insert_eq_of_mem hx₀],
--   filter_upwards [h2g, h2f, h4f],
--   intros x₂ hx₂ h2x₂ h3x₂,
--   symmetry,
--   rw [in_tangent_coordinates_core_eq],
--   swap, { rwa [extChartAt_source] at hx₂ },
--   swap, { rwa [extChartAt_source] at h3x₂ },
--   sorry,
--   -- rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
--   -- have hI := (contDiffWithinAt_ext_coord_change I (g x₂) (g x₀) $
--   --   PartialEquiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
--   --   .differentiable_within_at le_top,
--   -- have hI' := (contDiffWithinAt_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
--   --   PartialEquiv.mem_symm_trans_source _
--   --   (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
--   -- have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
--   -- refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
--   -- { exact λ x _, mem_range_self _ },
--   -- { exact λ x _, mem_range_self _ },
--   -- { simp_rw [written_in_extChartAt, function.comp_apply,
--   --     (extChartAt I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
--   -- { simp_rw [function.comp_apply, (extChartAt I (g x₀)).left_inv hx₂] }
-- end
-- lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
--   (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
--   (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
--   cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
--     (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
-- begin
--   sorry
-- end
theorem contMDiffAt_tangentBundle_trivializationAt_continuousLinearMap (x₀ : TangentBundle I M) :
    ContMDiffAt I.tangent 𝓘(𝕜, E) m
      (fun x : TangentBundle I M ↦
        (trivializationAt E (TangentSpace I) x₀.proj).continuousLinearMapAt 𝕜 x.proj x.2)
      x₀ := by
  let e := trivializationAt E (TangentSpace I) x₀.proj
  refine' ContMDiffAt.congr_of_eventuallyEq ?_ ?_
  pick_goal 3
  have h1 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt _ _ _)
  filter_upwards [h1] with x hx
  rw [Trivialization.continuousLinearMapAt_apply, e.coe_linearMapAt_of_mem hx]
  exact (e.smoothAt I <| mem_baseSet_trivializationAt E _ _).snd.of_le (sup_eq_left.mp rfl)

/-- Not useful by itself. TODO: generalize to `contMDiffWithinAt` of `tangentMapWithin` -/
theorem ContMDiffAt.contMDiffAt_tangentMap (x₀ : TangentBundle I M)
    (hf : ContMDiffAt I I' n f x₀.proj) (hmn : m + 1 ≤ n) :
    ContMDiffAt I.tangent I'.tangent m (tangentMap I I' f) x₀ := by
  rw [contMDiffAt_totalSpace]
  refine ⟨(hf.comp x₀ (contMDiffAt_proj (TangentSpace I))).of_le <| sorry, ?_⟩
  dsimp only [tangentMap]
  let e := trivializationAt E (TangentSpace I) x₀.proj
  let e' := trivializationAt E' (TangentSpace I') (f x₀.proj)
  have : ContMDiffAt I.tangent 𝓘(𝕜, E') m
      (fun x : TangentBundle I M ↦
        inTangentCoordinates I I' id f (mfderiv I I' f) x₀.proj x.proj <|
          e.continuousLinearMapAt 𝕜 x.proj x.2) x₀ := by
    sorry /-apply ContMDiffAt.mfderiv_apply (fun _ ↦ f) id TotalSpace.proj
      (fun x ↦ e.continuousLinearMapAt 𝕜 x.proj x.2) _ contMDiffAt_id (contMDiffAt_proj _) _
      hmn
    apply ContMDiffAt.comp (x₀.proj, x₀.proj) hf contMDiffAt_snd
    apply contMDiffAt_tangentBundle_trivializationAt_continuousLinearMap -/
    --exact this.congr_of_eventually_eq _
  have h1 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt _ _ _)
  have h2 :=
    (hf.continuousAt.comp (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt).preimage_mem_nhds
      (e'.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt _ _ _)
  sorry /-filter_upwards [h1, h2] with x hx h2x
  dsimp only [inTangentCoordinates, in_coordinates, id_def]
  simp_rw [ContinuousLinearMap.comp_apply, e.symmL_continuous_linear_map_at hx,
    Trivialization.continuousLinearMapAt_apply, e'.coe_linear_map_at_of_mem h2x] -/

end SmoothManifoldWithCorners
