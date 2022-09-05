import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable
import to_mathlib.topology.algebra.module

open bundle set function filter
open_locale manifold topological_space

namespace set

variables {α β γ δ : Type*} {f : α → β → γ} {s s₁ : set α} {t t₁ : set β} {x : α} {y : β}

lemma image2.some_prop (z : image2 f s t) : ∃ (y : s × t), f y.1 y.2 = z :=
let ⟨_, ⟨x, y, hx, hy, rfl⟩⟩ := z in ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

/-- Choose arbitrary elements in the domain mapped to `z`. Probably not mathlib-worthy. -/
noncomputable def image2.some (f : α → β → γ) (s : set α) (t : set β) (z : image2 f s t) : s × t :=
classical.some (image2.some_prop z)

lemma image2.some_spec (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) :
  (λ x : s × t, f x.1 x.2) (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩) = f x y :=
classical.some_spec (image2.some_prop ⟨f x y, mem_image2_of_mem hx hy⟩)

lemma image2.some_spec_fst (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ y' ∈ t,
  f (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1 y' = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2, subtype.mem _, image2.some_spec f hx hy⟩

lemma image2.some_spec_snd (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ x' ∈ s,
  f x' (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2 = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1, subtype.mem _, image2.some_spec f hx hy⟩

end set

section charted_space

variables {M H : Type*} [topological_space M] [topological_space H] [charted_space H M]
  (G : structure_groupoid H)

variables (H)
lemma mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
mem_chart_source H x
variables {H}

end charted_space

@[simp]
lemma local_equiv.refl_prod_refl {α β : Type*} :
  (local_equiv.refl α).prod (local_equiv.refl β) = local_equiv.refl (α × β) :=
by { ext1 ⟨x, y⟩, { refl }, { rintro ⟨x, y⟩, refl }, exact univ_prod_univ }

@[simp]
lemma local_homeomorph.refl_prod_refl {α β : Type*} [topological_space α] [topological_space β] :
  (local_homeomorph.refl α).prod (local_homeomorph.refl β) = local_homeomorph.refl (α × β) :=
by { ext1 ⟨x, y⟩, { refl }, { rintro ⟨x, y⟩, refl }, exact univ_prod_univ }

namespace model_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

lemma preimage_image (s : set H) : I ⁻¹' (I '' s) = s :=
I.injective.preimage_image s

end model_with_corners


namespace set

variables {α β γ δ : Type*}
lemma image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : set α} :
  (λ x, (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) :=
by { rintros _ ⟨x, hx, rfl⟩, exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx) }

-- lemma insert_prod_subset {s : set α} {t : set β} {x : α} {y : β} :
--   insert (x, y) (s ×ˢ t) = (insert x

lemma maps_to.subset_preimage {f : α → β} {s : set α} {t : set β} (hf : maps_to f s t) :
  s ⊆ f ⁻¹' t := hf

end set
open set


namespace asymptotics
variables {α E F E' F' : Type*} [topological_space α] [has_norm E] [has_norm E']
variables [seminormed_add_comm_group F] [seminormed_add_comm_group F']
variables {x : α} {s : set α}

lemma is_O_with_insert {C : ℝ} {g : α → E} {g' : α → E'} (h : ∥g x∥ ≤ C * ∥g' x∥) :
  is_O_with C (𝓝[insert x s] x) g g' ↔ is_O_with C (𝓝[s] x) g g' :=
by simp_rw [is_O_with, nhds_within_insert, eventually_sup, eventually_pure, h, true_and]

lemma is_o_insert {g : α → F} {g' : α → F'} (h : g x = 0) :
  g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
begin
  simp_rw [is_o],
  refine forall_congr (λ c, forall_congr (λ hc, _)),
  rw [is_O_with_insert],
  rw [h, norm_zero],
  exact mul_nonneg hc.le (norm_nonneg _)
end

end asymptotics


section fderiv

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']


section -- basic topology

variables {α β : Type*} [topological_space α] [topological_space β] {x y : α} {s s' t : set α}

lemma insert_mem_nhds_within_of_subset_insert [t1_space α] (hu : t ⊆ insert y s) :
  insert x s ∈ 𝓝[t] x :=
begin
  rcases eq_or_ne x y with rfl|h,
  { exact mem_of_superset self_mem_nhds_within hu },
  rw [← union_singleton, union_comm, ← diff_subset_iff, diff_eq] at hu,
  exact mem_of_superset (inter_mem_nhds_within _ (compl_singleton_mem_nhds h))
    (hu.trans (subset_insert _ _)),
end

lemma prod_mem_nhds_within {t t' : set β} {x : α × β}
  (hs : s ∈ 𝓝[s'] x.1) (ht : t ∈ 𝓝[t'] x.2) : s ×ˢ t ∈ 𝓝[s' ×ˢ t'] x :=
begin
  rw [mem_nhds_within] at hs ht ⊢,
  obtain ⟨u, hu, hxu, hus⟩ := hs,
  obtain ⟨v, hv, hxv, hvt⟩ := ht,
  exact ⟨u ×ˢ v, hu.prod hv, ⟨hxu, hxv⟩, prod_inter_prod.subset.trans $ prod_mono hus hvt⟩,
end


end

section

variables {f : E → F} {s : set E} {x : E} {f' : E →L[𝕜] F} {n : ℕ∞}

theorem has_fderiv_within_at.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : tendsto f (𝓝[s] x) (𝓝[t] f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
has_fderiv_at_filter.comp x hg hf hst

lemma cont_diff_within_at.comp_of_mem
  {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E)
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_diff_within_at 𝕜 n f s x) (hs : t ∈ 𝓝[f '' s] f x) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
(hg.mono_of_mem hs).comp x hf (subset_preimage_image f s)

end


variables {f : G → E → F} {g : G → E} {s : set G} {t : set E} {x : G} {n m : ℕ∞} {u : set (G × E)}


lemma has_fderiv_within_at_insert {g' : G →L[𝕜] E} :
  has_fderiv_within_at g g' (insert x s) x ↔ has_fderiv_within_at g g' s x :=
begin
  simp_rw [has_fderiv_within_at, has_fderiv_at_filter],
  rw [asymptotics.is_o_insert],
  simp only [sub_self, g'.map_zero]
end

alias has_fderiv_within_at_insert ↔ has_fderiv_within_at.of_insert has_fderiv_within_at.insert

lemma cont_diff_within_at_insert :
  cont_diff_within_at 𝕜 n g (insert x s) x ↔ cont_diff_within_at 𝕜 n g s x :=
by simp_rw [cont_diff_within_at, insert_eq_of_mem (mem_insert _ _)]

alias cont_diff_within_at_insert ↔ cont_diff_within_at.of_insert cont_diff_within_at.insert

lemma has_fderiv_within_at_diff_singleton {g' : G →L[𝕜] E} :
  has_fderiv_within_at g g' (s \ {x}) x ↔ has_fderiv_within_at g g' s x :=
by rw [← has_fderiv_within_at_insert, insert_diff_singleton, has_fderiv_within_at_insert]

-- replaces 2 mathlib lemmas
lemma cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem' {f : E → F} {s : set E} {x : E}
  {n : ℕ} :
  cont_diff_within_at 𝕜 (n + 1 : ℕ) f s x
  ↔ ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → E →L[𝕜] F,
    (∀ x ∈ u, has_fderiv_within_at f (f' x) s x) ∧ cont_diff_within_at 𝕜 n f' s x :=
begin
  refine ⟨λ hf, hf.has_fderiv_within_at_nhds, _⟩,
  rw [← cont_diff_within_at_insert, cont_diff_within_at_succ_iff_has_fderiv_within_at,
    insert_eq_of_mem (mem_insert _ _)],
  rintro ⟨u, hu, hus, f', huf', hf'⟩,
  refine ⟨u, hu, f', λ y hy, (huf' y hy).insert.mono_of_mem _, hf'.insert.mono hus⟩,
  exact insert_mem_nhds_within_of_subset_insert hus,
end

-- is this true?
-- lemma cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem'' {f : E → F} {s : set E} {x : E}
--   {n : ℕ} :
--   cont_diff_within_at 𝕜 (n + 1 : ℕ) f s x
--   ↔ ∃ u ∈ 𝓝[s] x, u ⊆ s ∧ ∃ f' : E → E →L[𝕜] F,
--     (∀ x' ∈ u, has_fderiv_within_at f (f' x') s x') ∧ cont_diff_within_at 𝕜 n f' s x :=
-- begin
--   rw [cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem'],
--   split,
--   { rintro ⟨u, hu, hus, f', huf', hf'⟩,
--     refine ⟨u ∩ s, inter_mem (nhds_within_mono x (subset_insert x s) hu) self_mem_nhds_within,
--       inter_subset_right _ _, f', _, hf'⟩,
--     exact λ x hx, huf' x hx.1 },
--   rintro ⟨u, hu, hus, f', huf', hf'⟩,
--   refine ⟨insert x u, insert_mem_nhds_within_insert hu, insert_subset_insert hus, f', _, hf'⟩,
--   rintro x' (rfl|hx'),
--   { admit },
--   exact huf' x' hx'
-- end

/-- One direction of `cont_diff_within_at_succ_iff_has_fderiv_within_at`, but where all derivatives
  are taken within the same set. Version for partial derivatives. -/
-- probably an iff, do we need x ∈ s?
lemma cont_diff_within_at.has_fderiv_within_at_nhds₂ {n : ℕ}
  (hf : cont_diff_within_at 𝕜 (n+1) (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 n g s x)
  (hst : insert x s ×ˢ t ⊆ u) -- maybe weaken
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) :
  ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : G → E →L[𝕜] F,
    (∀ x ∈ u, has_fderiv_within_at (f x) (f' x) t (g x)) ∧
    cont_diff_within_at 𝕜 n (λ x, f' x) s x :=
begin
  obtain ⟨v, hv, hvs, f', hvf', hf'⟩ := hf.has_fderiv_within_at_nhds,
  refine ⟨(λ z, (z, g z)) ⁻¹' v ∩ insert x s, _, inter_subset_right _ _,
    λ z, (f' (z, g z)).comp (continuous_linear_map.inr 𝕜 G E), _, _⟩,
  { refine inter_mem _ self_mem_nhds_within,
    have := mem_of_mem_nhds_within (mem_insert _ _) hv,
    refine mem_nhds_within_insert.mpr ⟨this, _⟩,
    refine (continuous_within_at_id.prod hg.continuous_within_at).preimage_mem_nhds_within' _,
    rw [← nhds_within_le_iff] at hu hv ⊢,
    refine (hu.trans $ nhds_within_mono _ $ subset_insert _ _).trans hv },
  { intros z hz,
    have := hvf' (z, g z) hz.1,
    refine this.comp (g z) (has_fderiv_at_prod_mk_right _ _).has_fderiv_within_at _,
    exact maps_to'.mpr ((image_prod_mk_subset_prod_right hz.2).trans hst) },
  { exact (hf'.continuous_linear_map_comp $ (continuous_linear_map.compL 𝕜 E (G × E) F).flip
      (continuous_linear_map.inr 𝕜 G E)).comp_of_mem x
      (cont_diff_within_at_id.prod hg) hu },
end

-- simplify/replace mathlib lemmas using this
lemma cont_diff_within_at.fderiv_within₂'
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : ∀ᶠ y in 𝓝[insert x s] x, unique_diff_within_at 𝕜 t (g y))
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
begin
  have : ∀ k : ℕ, (k : with_top ℕ) ≤ m →
    cont_diff_within_at 𝕜 k (λ x, fderiv_within 𝕜 (f x) t (g x)) s x,
  { intros k hkm,
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le $ (add_le_add_right hkm 1).trans hmn).has_fderiv_within_at_nhds₂ (hg.of_le hkm)
      hst hu,
    refine hf'.congr_of_eventually_eq_insert _,
    filter_upwards [hv, ht],
    exact λ y hy h2y, (hvf' y hy).fderiv_within h2y },
  induction m using with_top.rec_top_coe,
  { obtain rfl := eq_top_iff.mpr hmn,
    rw [cont_diff_within_at_top],
    exact λ m, this m le_top },
  exact this m le_rfl
end

lemma cont_diff_within_at_fderiv_within'
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : (m + 1 : with_top ℕ) ≤ n)
  (hst : insert x s ×ˢ t ⊆ u) -- maybe weaken
  (hgx : ∀ᶠ x' in 𝓝[insert x s] x, g x' ∈ t)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) -- remove
  :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
hf.fderiv_within₂' hg (hgx.mono (λ y hy, ht _ hy)) hmn hst hu

lemma cont_diff_within_at_fderiv_within
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : (m + 1 : with_top ℕ) ≤ n) (hx : x ∈ s)
  (hst : s ×ˢ t ⊆ u) -- maybe weaken
  (hgx : ∀ᶠ x' in 𝓝[s] x, g x' ∈ t)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) -- remove
  :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
by { rw [← insert_eq_self.mpr hx] at hst hgx,
  exact cont_diff_within_at_fderiv_within' hf hg ht hmn hst hgx hu }

end fderiv

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x : M}

attribute [ext] model_with_corners charted_space
lemma model_with_corners_self_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) :=
by { ext1, simp }

lemma model_with_corners.range_prod : range (I.prod J) = range I ×ˢ range J :=
by { simp_rw [← model_with_corners.target_eq], refl }

lemma charted_space_self_prod : prod_charted_space E E F F = charted_space_self (E × F) :=
by { ext1, simp [prod_charted_space, atlas], ext1, simp, }


lemma ext_chart_preimage_mem_nhds_within_range {x' : M} {t : set M}
  (h : x' ∈ (ext_chart_at I x).source) (ht : t ∈ 𝓝 x') :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝[range I] ((ext_chart_at I x) x') :=
nhds_within_le_nhds $ ext_chart_preimage_mem_nhds' _ _ h ht

section boundary

variables (I M)

/-- An element is on the boundary of a manifold `M` if its chart maps it to the frontier of the
model space. Note: this also includes all corners of `M`. -/
def boundary : set M := {x : M | ext_chart_at I x x ∈ frontier (range I) }

variables {I M}

lemma mem_boundary {x : M} : x ∈ boundary I M ↔ ext_chart_at I x x ∈ frontier (range I) := iff.rfl

-- /-- All charts agree on whether you are at the boundary. -/
-- lemma mem_boundary_iff_of_mem {x x' : M} (hx : x ∈ (ext_chart_at I x').source) :
--   x ∈ boundary I M ↔ ext_chart_at I x' x ∈ frontier (range I) :=
-- by admit -- likely not going to be used

end boundary

namespace basic_smooth_vector_bundle_core
variables [smooth_manifold_with_corners I M] (Z : basic_smooth_vector_bundle_core I M E')

lemma coord_change_comp' {i j k : atlas H M} {x : M}
  (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (hk : x ∈ k.1.source) (v : E') :
  Z.coord_change j k (j x) (Z.coord_change i j (i x) v) = Z.coord_change i k (i x) v :=
begin
  rw [show j x = _, by rw [← i.1.left_inv hi]],
  apply Z.coord_change_comp,
  simp only [hi, hj, hk] with mfld_simps
end

lemma coord_change_self' {i : atlas H M} {x : M} (hi : x ∈ i.1.source) (v : E') :
  Z.coord_change i i (i x) v = v :=
Z.coord_change_self i (i x) (i.1.maps_to hi) v

lemma coord_change_comp_eq_self (i j : atlas H M) {x : H}
  (hx : x ∈ (i.1.symm.trans j.1).source) (v : E') :
  Z.coord_change j i (i.1.symm.trans j.1 x) (Z.coord_change i j x v) = v :=
begin
  rw [Z.coord_change_comp i j i x _ v, Z.coord_change_self _ _ hx.1],
  simp only with mfld_simps at hx,
  simp only [hx.1, hx.2] with mfld_simps
end

lemma coord_change_comp_eq_self' {i j : atlas H M} {x : M}
  (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (v : E') :
  Z.coord_change j i (j x) (Z.coord_change i j (i x) v) = v :=
by rw [Z.coord_change_comp' hi hj hi v, Z.coord_change_self' hi]

lemma chart_apply (z : Z.to_topological_vector_bundle_core.total_space) :
  Z.chart (chart_mem_atlas H x) z = (chart_at H x z.proj,
    Z.coord_change (achart H z.proj) (achart H x) (achart H z.proj z.proj) z.2) :=
rfl

lemma smooth_iff_target {f : N → Z.to_topological_vector_bundle_core.total_space} :
  smooth J (I.prod 𝓘(𝕜, E')) f ↔ continuous (bundle.total_space.proj ∘ f) ∧
  ∀ x, smooth_at J 𝓘(𝕜, E × E') (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
by simp_rw [smooth, smooth_at, cont_mdiff, Z.cont_mdiff_at_iff_target, forall_and_distrib,
  continuous_iff_continuous_at]

end basic_smooth_vector_bundle_core

lemma cont_diff_within_at.comp_cont_mdiff_within_at
  {g : F → F''} {f : M → F} {s : set M} {t : set F} {x : M}
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F) n f s x) (h : s ⊆ f ⁻¹' t) :
  cont_mdiff_within_at I 𝓘(𝕜, F'') n (g ∘ f) s x :=
begin
  rw cont_mdiff_within_at_iff at *,
  refine ⟨hg.continuous_within_at.comp hf.1 h, _⟩,
  rw [← (ext_chart_at I x).left_inv (mem_ext_chart_source I x)] at hg,
  apply cont_diff_within_at.comp _ (by exact hg) hf.2 _,
  exact (inter_subset_left _ _).trans (preimage_mono h)
end

lemma cont_diff_at.comp_cont_mdiff_at {g : F → F''} {f : M → F} {x : M}
  (hg : cont_diff_at 𝕜 n g (f x)) (hf : cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F'') n (g ∘ f) x :=
hg.comp_cont_mdiff_within_at hf subset.rfl

lemma cont_diff.comp_cont_mdiff {g : F → F''} {f : M → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_mdiff I 𝓘(𝕜, F) n f) :
  cont_mdiff I 𝓘(𝕜, F'') n (g ∘ f) :=
λ x, hg.cont_diff_at.comp_cont_mdiff_at (hf x)

lemma smooth_within_at.mdifferentiable_within_at
  (hf : smooth_within_at I I' f s x) : mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_within_at le_top

lemma smooth_at.mdifferentiable_at (hf : smooth_at I I' f x) : mdifferentiable_at I I' f x :=
hf.mdifferentiable_at le_top

lemma smooth_on.mdifferentiable_on (hf : smooth_on I I' f s) : mdifferentiable_on I I' f s :=
hf.mdifferentiable_on le_top

lemma smooth_at.comp {g : M → M'} {f : N → M} (x : N)
  (hg : smooth_at I I' g (f x)) (hf : smooth_at J I f x) : smooth_at J I' (g ∘ f) x :=
hg.comp x hf

lemma smooth.comp {g : M → M'} {f : N → M}
  (hg : smooth I I' g) (hf : smooth J I f) : smooth J I' (g ∘ f) :=
hg.comp hf

lemma smooth_at.fst {f : N → M × M'} {x : N} (hf : smooth_at J (I.prod I') f x) :
  smooth_at J I (λ x, (f x).1) x :=
smooth_at_fst.comp x hf

lemma smooth_at.snd {f : N → M × M'} {x : N} (hf : smooth_at J (I.prod I') f x) :
  smooth_at J I' (λ x, (f x).2) x :=
smooth_at_snd.comp x hf

lemma smooth.fst {f : N → M × M'} (hf : smooth J (I.prod I') f) :
  smooth J I (λ x, (f x).1) :=
smooth_fst.comp hf

lemma smooth.snd {f : N → M × M'} (hf : smooth J (I.prod I') f) :
  smooth J I' (λ x, (f x).2) :=
smooth_snd.comp hf

lemma smooth_prod_assoc :
  smooth ((I.prod I').prod J) (I.prod (I'.prod J)) (λ x : (M × M') × N, (x.1.1, x.1.2, x.2)) :=
smooth_fst.fst.prod_mk $ smooth_fst.snd.prod_mk smooth_snd

lemma ext_chart_at_prod (x : M × M') :
  ext_chart_at (I.prod I') x = (ext_chart_at I x.1).prod (ext_chart_at I' x.2) :=
by simp only with mfld_simps

-- the following proof takes very long in pure term mode
lemma cont_mdiff_at.clm_comp {g : M → F →L[𝕜] F''} {f : M → F' →L[𝕜] F} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F →L[𝕜] F'') n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] F'') n (λ x, (g x).comp (f x)) x :=
@cont_diff_at.comp_cont_mdiff_at 𝕜 _ E _ _ ((F →L[𝕜] F'') × (F' →L[𝕜] F)) _ _ _ _ _ _ _ _
  _ _ _ _
  (λ x, x.1.comp x.2) (λ x, (g x, f x)) x
  (by { apply cont_diff.cont_diff_at, apply is_bounded_bilinear_map.cont_diff,
    exact is_bounded_bilinear_map_comp })
  (hg.prod_mk_space hf)

lemma cont_mdiff.clm_comp {g : M → F →L[𝕜] F''} {f : M → F' →L[𝕜] F}
  (hg : cont_mdiff I 𝓘(𝕜, F →L[𝕜] F'') n g) (hf : cont_mdiff I 𝓘(𝕜, F' →L[𝕜] F) n f) :
  cont_mdiff I 𝓘(𝕜, F' →L[𝕜] F'') n (λ x, (g x).comp (f x)) :=
λ x, (hg x).clm_comp (hf x)

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

-- this can be useful to see where we (ab)use definitional equalities
-- local attribute [irreducible] tangent_space

/-!
I don't know if these instances were intentionally not declared for `tangent_space`
(maybe to not endow it with a particular norm), but if we don't want them we need to redesign some
other things.
Note that `dual_pair.update` wants `F` to be a `normed_add_comm_group` (which seems to be pretty
necessary for the definition -- although maybe we can get away with `has_continuous_smul` by
redesigning some things?).
In `rel_mfld.slice` we use `dual_pair.update` applied to `tangent_space`. If we don't add these
instances, it is a miracle that Lean still accepts the definition, but what is going on is that Lean
is unfolding the definition of `tangent_space`, realizing that `tangent_space I x = E` and
`tangent_space I' y = E'` and using the `normed_add_comm_group` instances of these types.
Note that this still uses these instances in a very sneaky way for the tangent space, but with
additional detriment that up to reducible transparancy, the term is not type-correct
(in other words: you have to unfold `tangent_space` to realize that the term is type-correct).
This means that many tactics, like `simp`, `rw` and `dsimp` fail to rewrite within this term,
because the result is not type correct up to reducible transparancy.
This is a nightmare, so we declare these instances.
(at least, this is what I think was going on, but unfortunately some issues still persisted after
this.) -/
instance {x : M} : normed_add_comm_group (tangent_space I x) := by delta_instance tangent_space
instance {x : M} : normed_space 𝕜 (tangent_space I x) := by delta_instance tangent_space

lemma tangent_bundle_core_coord_change_achart (x x' : M) (z : H) :
  (tangent_bundle_core I M).coord_change (achart H x) (achart H x') z =
  fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm) (range I) (I z) :=
rfl

variables (I)

lemma cont_diff_on_coord_change' {e e' : local_homeomorph M H}
  (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

variables {I}
/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr_point {x' : M} (h : x = x') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') :=
by subst h

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr {f' : M → M'} (h : f = f') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) :=
by subst h

/-- The derivative of the projection `M × M' → M` is the projection `TM × TM' → TM` -/
lemma mfderiv_fst (x : M × M') :
  mfderiv (I.prod I') I prod.fst x = continuous_linear_map.fst 𝕜 E E' :=
begin
  simp_rw [mfderiv, dif_pos smooth_at_fst.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I x.1).right_inv ((ext_chart_at I x.1).maps_to $
      mem_ext_chart_source I x.1) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.1 },
  exact fderiv_within_fst this,
end

/-- The derivative of the projection `M × M' → M'` is the projection `TM × TM' → TM'` -/
lemma mfderiv_snd (x : M × M') :
  mfderiv (I.prod I') I' prod.snd x = continuous_linear_map.snd 𝕜 E E' :=
begin
  simp_rw [mfderiv, dif_pos smooth_at_snd.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I' x.2).right_inv ((ext_chart_at I' x.2).maps_to $
      mem_ext_chart_source I' x.2) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.2 },
  exact fderiv_within_snd this,
end

lemma mdifferentiable_at.prod_mk {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mdifferentiable_at J (I.prod I') (λ x, (f x, g x)) x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩


-- todo: rename differentiable_at.fderiv_within_prod -> differentiable_within_at.fderiv_within_prod
lemma mdifferentiable_at.mfderiv_prod {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mfderiv J (I.prod I') (λ x, (f x, g x)) x = (mfderiv J I f x).prod (mfderiv J I' g x) :=
begin
  classical,
  simp_rw [mfderiv, dif_pos (hf.prod_mk hg), dif_pos hf, dif_pos hg],
  exact differentiable_at.fderiv_within_prod hf.2 hg.2 (J.unique_diff _ (mem_range_self _))
end

lemma mfderiv_prod_eq_add {f : N × M → M'} {p : N × M}
  (hf : mdifferentiable_at (J.prod I) I' f p) :
  mfderiv (J.prod I) I' f p =
  (show F × E →L[𝕜] E', from mfderiv (J.prod I) I' (λ (z : N × M), f (z.1, p.2)) p +
  mfderiv (J.prod I) I' (λ (z : N × M), f (p.1, z.2)) p) :=
begin
  dsimp only,
  rw [← @prod.mk.eta _ _ p] at hf,
  rw [mfderiv_comp p (by apply hf) (smooth_fst.prod_mk smooth_const).mdifferentiable_at,
    mfderiv_comp p (by apply hf) (smooth_const.prod_mk smooth_snd).mdifferentiable_at,
    ← continuous_linear_map.comp_add,
    smooth_fst.mdifferentiable_at.mfderiv_prod smooth_const.mdifferentiable_at,
    smooth_const.mdifferentiable_at.mfderiv_prod smooth_snd.mdifferentiable_at,
    mfderiv_fst, mfderiv_snd, mfderiv_const, mfderiv_const],
  symmetry,
  convert continuous_linear_map.comp_id _,
  { exact continuous_linear_map.fst_prod_zero_add_zero_prod_snd },
  simp_rw [prod.mk.eta],
end

/-- When `ϕ` is a continuous linear map that changes vectors in charts around `x` to vectors
  in charts around `y`, `in_coordinates' Z Z' x₀ x y₀ y ϕ` is a coordinate change of this continuous
  linear map that makes sense from charts around `x₀` to charts around `y₀`
  by composing it with appropriate coordinate changes given by smooth vector bundles `Z` and `Z'`.
  -/
def in_coordinates' (Z : basic_smooth_vector_bundle_core I M F)
  (Z' : basic_smooth_vector_bundle_core I' M' F')
  (x₀ x : M) (y₀ y : M') (ϕ : F →L[𝕜] F') : F →L[𝕜] F' :=
Z'.coord_change (achart H' y) (achart H' y₀) (chart_at H' y y) ∘L ϕ ∘L
  Z.coord_change (achart H x₀) (achart H x) (chart_at H x₀ x)

variables (I I')
/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
  in charts around `g x`, `in_coordinates I I' f g ϕ x₀ x` is a coordinate change of this continuous
  linear map that makes sense from charts around `f x₀` to charts around `g x₀`
  by composing it with appropriate coordinate changes. -/
noncomputable def in_coordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') :
  N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates' (tangent_bundle_core I M) (tangent_bundle_core I' M')
  (f x₀) (f x) (g x₀) (g x) (ϕ x)

variables {I I'}

/-- The appropriate (more general) formulation of `cont_mdiff_at.mfderiv''`. Used in `curry`. -/
lemma cont_mdiff_at.mfderiv''' {x : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x, g x))
  (hg : cont_mdiff_at J I m g x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x', mfderiv I I' (f x') (g x')) x) x :=
begin
  have h4f : continuous_at (λ x, f x (g x)) x,
  { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have h2f : ∀ᶠ x₂ in 𝓝 x, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  { refine ((continuous_at_id.prod hg.continuous_at).eventually h3f).mono (λ x hx, _),
    exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)),
  have : cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜
    (ext_chart_at I' (f x (g x)) ∘ f ((ext_chart_at J x).symm x') ∘ (ext_chart_at I (g x)).symm)
    (range I) (ext_chart_at I (g x) (g ((ext_chart_at J x).symm x'))))
    (range J) (ext_chart_at J x x),
  { rw [cont_mdiff_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
    refine (cont_diff_within_at_fderiv_within _ (hg.2.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
    swap 3,
    { simp_rw [function.comp, ext_chart_at_to_inv],
      refine hf.2 },
    { refine (ext_chart_at J x).target ∩
      (λ x', (ext_chart_at J x).symm x') ⁻¹' (g ⁻¹' (ext_chart_at I (g x)).source) },
    { exact mem_of_superset self_mem_nhds_within
        ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x) },
    { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
      exact ⟨local_equiv.maps_to _ (mem_ext_chart_source J x), mem_ext_chart_source I (g x)⟩ },
    { simp_rw [model_with_corners.range_prod],
      exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x)
        subset_rfl },
    { refine eventually_of_forall (λ x', mem_range_self _) },
    swap 2, { refine inter_mem (ext_chart_at_target_mem_nhds_within J x) _,
      refine ext_chart_preimage_mem_nhds_within_range (mem_ext_chart_source J x) _,
      exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)) },
    simp_rw [function.comp, model_with_corners.range_prod, ext_chart_at_to_inv],
    refine mem_of_superset self_mem_nhds_within _,
    refine image_prod_mk_subset_prod.trans (prod_mono _ _),
    { rw [image_id'],
      exact ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x) },
    rintro _ ⟨x', hx', rfl⟩,
    refine ext_chart_at_target_subset_range I (g x) _,
    exact (ext_chart_at I (g x)).maps_to hx'.2 },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ f x' ∘ (ext_chart_at I (g x)).symm)
    (range I) (ext_chart_at I (g x) (g x'))) x,
  { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm ∘
      written_in_ext_chart_at I I' (g x') (f x') ∘ ext_chart_at I (g x') ∘
      (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))) x,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x' ∈ (ext_chart_at I (g x)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x)).symm) x' =
      ext_chart_at I' (f x (g x)) (f x₂ ((ext_chart_at I (g x)).symm x')),
    { rintro x' ⟨hx', h2x'⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx', (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x'] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_preimage_mem_nhds' _ _ hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is the same as the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  change cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', (fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm)
        (range I') (ext_chart_at I' (f x' (g x')) (f x' (g x')))).comp
        ((mfderiv I I' (f x') (g x')).comp (fderiv_within 𝕜 (ext_chart_at I (g x') ∘
        (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))))) x,
  refine this.congr_of_eventually_eq _,
  filter_upwards [h2g, h2f,
    h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x (g x)))],
  intros x₂ hx₂ h2x₂ h3x₂,
  symmetry,
  rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
  have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x) $
    local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
    .differentiable_within_at le_top,
  have hI' := (cont_diff_within_at_ext_coord_change I' (f x (g x)) (f x₂ (g x₂)) $
    local_equiv.mem_symm_trans_source _
    (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
  have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
  refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
  { exact λ x _, mem_range_self _ },
  { exact λ x _, mem_range_self _ },
  { simp_rw [written_in_ext_chart_at, function.comp_apply,
      (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
  { simp_rw [function.comp_apply, (ext_chart_at I (g x)).left_inv hx₂] }
end

/-- The map `D_xf(x,y)` is `C^n` as a continuous linear map, assuming that `f` is a `C^(n+1)` map
between manifolds.
We have to insert appropriate coordinate changes to make sense of this statement.
This statement is general enough to work for partial derivatives / functions with parameters. -/
lemma cont_mdiff_at.mfderiv'' (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x, x)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' id (λ x, f x x) (λ x', mfderiv I I' (f x') x') x) x :=
hf.mfderiv''' f id cont_mdiff_at_id hmn

/-- The map `mfderiv f` is `C^n` as a continuous linear map, assuming that `f` is `C^(n+1)`.
We have to insert appropriate coordinate changes to make sense of this statement. -/
lemma cont_mdiff_at.mfderiv' {f : M → M'}
  (hf : cont_mdiff_at I I' n f x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_coordinates I I' id f (mfderiv I I' f) x) x :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x, x) :=
  cont_mdiff_at.comp (x, x) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv'' (λ x, f) this hmn
  -- apply cont_mdiff_at.mfderiv''' (λ x, f) id this cont_mdiff_at_id hmn
end

instance has_smooth_add_self : has_smooth_add 𝓘(𝕜, F) F :=
⟨by { convert cont_diff_add.cont_mdiff, exact model_with_corners_self_prod.symm,
  exact charted_space_self_prod }⟩

end smooth_manifold_with_corners

section maps

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F G'}

variables {M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{N : Type*} [topological_space N] [charted_space G N]
{N' : Type*} [topological_space N'] [charted_space G' N']
{n : ℕ∞}
(f : C^∞⟮I, M; J, N⟯)

namespace cont_mdiff_map

instance : continuous_map_class C^n⟮I, M; J, N⟯ M N :=
{ coe := coe_fn,
  coe_injective' := coe_inj,
  map_continuous := λ f, f.cont_mdiff_to_fun.continuous }

/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

/-- Given two smooth maps `f` and `g`, this is the smooth map `(x, y) ↦ (f x, g y)`. -/
def prod_mk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
⟨λ x, (f x, g x), f.2.prod_mk g.2⟩

end cont_mdiff_map

namespace diffeomorph

instance : continuous_map_class (M ≃ₘ⟮I, J⟯ N) M N :=
{ coe := coe_fn,
  coe_injective' := coe_fn_injective,
  map_continuous := λ f, f.continuous }

end diffeomorph

end maps
