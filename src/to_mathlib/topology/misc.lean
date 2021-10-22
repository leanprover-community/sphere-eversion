import topology.path_connected
import topology.uniform_space.compact_separated

noncomputable theory

open set function filter
open_locale unit_interval topological_space uniformity filter

section -- algebra.order.group

variables {α : Type*} [group α] [has_le α] [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)]

@[to_additive]
lemma le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 :=
by simp [div_eq_mul_inv]

end

section -- to bounded_lattice

variables {α β : Type*}

lemma function.surjective.map_top {f : α → β} (hf : surjective f) : filter.map f ⊤ = ⊤ :=
begin
  ext, simp only [mem_map, mem_top, eq_univ_iff_forall, mem_preimage],
  exact (@surjective.forall _ _ _ hf (∈ s)).symm,
end

end

section -- to data.set.intervals.proj_Icc

variables {α β : Type*} [linear_order α] {a b : α} {h : a ≤ b} {x : α}

lemma proj_Icc_eq_left : proj_Icc a b h x = ⟨a, left_mem_Icc.mpr h⟩ ↔ x ≤ a :=
sorry


lemma proj_Icc_eq_right : proj_Icc a b h x = ⟨b, right_mem_Icc.mpr h⟩ ↔ b ≤ x :=
sorry

end


section -- to unit_interval

@[simp] lemma proj_Icc_eq_zero {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
proj_Icc_eq_left

@[simp] lemma proj_Icc_eq_one {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
proj_Icc_eq_right

end



section -- to topology.algebra.ordered.proj_Icc

variables {α β γ : Type*} [linear_order α] [topological_space γ] {a b c : α} {h : a ≤ b}

lemma filter.tendsto.Icc_extend (f : γ → Icc a b → β) {z : γ} {l : filter α} {l' : filter β}
  (hf : tendsto ↿f (𝓝 z ×ᶠ l.map (proj_Icc a b h)) l') :
  tendsto ↿(Icc_extend h ∘ f) (𝓝 z ×ᶠ l) l' :=
show tendsto (↿f ∘ prod.map id (proj_Icc a b h)) (𝓝 z ×ᶠ l) l', from
hf.comp $ tendsto_id.prod_map tendsto_map

variables [topological_space α] [order_topology α] [topological_space β]

lemma continuous.Icc_extend' {f : γ → Icc a b → β}
  (hf : continuous ↿f) : continuous ↿(Icc_extend h ∘ f) :=
hf.comp $ continuous_id.prod_map continuous_proj_Icc

lemma continuous_at.Icc_extend {x : γ} (f : γ → Icc a b → β)
  (hf : continuous_at ↿f (x, proj_Icc a b h c)) : continuous_at ↿(Icc_extend h ∘ f) (x, c) :=
show continuous_at (↿f ∘ prod.map id (proj_Icc a b h)) (x, c), from
continuous_at.comp hf (continuous_id.prod_map continuous_proj_Icc).continuous_at

end

section -- to topology.path_connected

variables {X Y Z : Type*} [topological_space X] [topological_space Y]
  [topological_space Z] {x y : X}

lemma continuous.extend' {γ : Y → path x y} (hγ : continuous ↿γ) :
  continuous ↿(λ t, (γ t).extend) :=
continuous.Icc_extend' hγ

lemma filter.tendsto.extend {X Y : Type*} [topological_space X] [topological_space Y]
  {l r : Y → X}
  {y : Y} {l₁ : filter ℝ} {l₂ : filter X} {γ : ∀ y, path (l y) (r y)}
  (hγ : tendsto ↿γ (𝓝 y ×ᶠ l₁.map (proj_Icc 0 1 zero_le_one)) l₂) :
  tendsto ↿(λ t, (γ t).extend) (𝓝 y ×ᶠ l₁) l₂ :=
filter.tendsto.Icc_extend _ hγ

lemma continuous.extend {f : Z → Y} {g : Z → ℝ} {γ : Y → path x y} (hγ : continuous ↿γ)
  (hf : continuous f) (hg : continuous g) :
  continuous (λ i, (γ (f i)).extend (g i)) :=
(continuous.extend' hγ).comp $ hf.prod_mk hg

lemma continuous_at.extend {f : Z → Y} {g : Z → ℝ} {l r : Y → X} (γ : ∀ y, path (l y) (r y))
  {z : Z}
  (hγ : continuous_at ↿γ (f z, proj_Icc 0 1 zero_le_one (g z))) (hf : continuous_at f z)
  (hg : continuous_at g z) : continuous_at (λ i, (γ (f i)).extend (g i)) z :=
show continuous_at
  ((λ p : Y × ℝ, (Icc_extend (@zero_le_one ℝ _) (γ p.1) p.2)) ∘ (λ i, (f i, g i))) z, from
continuous_at.comp (continuous_at.Icc_extend (λ x y, γ x y) hγ) $ hf.prod hg

end
section -- to topology.algebra.group_with_zero

variables {α G₀ β γ : Type*} [group_with_zero G₀] [topological_space G₀]
  [has_continuous_inv₀ G₀] [has_continuous_mul G₀]

lemma continuous_at.comp_div_cases {f g : α → G₀} {k : α → γ} (h : γ → G₀ → β)
  [topological_space α] [topological_space β] [topological_space γ] {a : α}
  (hk : continuous_at k a) (hf : continuous_at f a) (hg : continuous_at g a)
  (hh : g a ≠ 0 → continuous_at ↿h (k a, f a / g a))
  (h2h : g a = 0 → tendsto ↿h (𝓝 (k a) ×ᶠ ⊤) (𝓝 (h (k a) 0))) :
  continuous_at (λ x, h (k x) (f x / g x)) a :=
begin
  show continuous_at (↿h ∘ (λ x, (k x, f x / g x))) a,
  by_cases hga : g a = 0,
  { rw [continuous_at], simp_rw [comp_app, hga, div_zero],
    exact (h2h hga).comp (hk.prod_mk tendsto_top) },
  { exact continuous_at.comp (hh hga) (hk.prod (hf.div hg hga)) }
end

end

section

section
variables {α : Type*} [uniform_space α]
-- to uniform_space/basic

-- `uniformity_eq_symm` should probably be reformulated in the library
lemma symm_eq_uniformity : map (@prod.swap α α) (𝓤 α) = 𝓤 α :=
uniformity_eq_symm.symm

lemma nhds_eq_comap_uniformity_rev {y : α} : 𝓝 y = (𝓤 α).comap (λ x, (x, y)) :=
by { rw [uniformity_eq_symm, map_swap_eq_comap_swap, comap_comap], exact nhds_eq_comap_uniformity }


end

-- to logic/basic
/-- We intentionally restrict the type of `α` here so that this is a safer for simp. -/
lemma imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ (∀ x, p → q x) :=
forall_swap

-- to filter/basic
lemma filter.mem_prod_top {α β : Type*} {f : filter α} {s : set (α × β)} :
  s ∈ f ×ᶠ (⊤ : filter β) ↔ {a | ∀ b, (a, b) ∈ s} ∈ f :=
begin
  nth_rewrite 1 [← exists_mem_subset_iff],
  simp only [mem_prod_iff, exists_prop, exists_eq_left, mem_top, prod_univ, mem_preimage,
    prod.forall, subset_def, mem_set_of_eq, imp_forall_iff]
end

-- to uniform_convergence
lemma tendsto_prod_top_iff {α β ι : Type*} [uniform_space β] (F : ι → α → β) {c : β}
  {p : filter ι} : tendsto ↿F (p ×ᶠ ⊤) (𝓝 c) ↔ tendsto_uniformly F (λ _, c) p :=
let j : β → β × β := prod.mk c in
calc tendsto ↿F (p ×ᶠ ⊤) (𝓝 c)
    ↔ map ↿F (p ×ᶠ ⊤) ≤ (𝓝 c) : iff.rfl
... ↔ map ↿F (p ×ᶠ ⊤) ≤ comap j (𝓤 β) : by rw nhds_eq_comap_uniformity
... ↔ map j (map ↿F (p ×ᶠ ⊤)) ≤ 𝓤 β : map_le_iff_le_comap.symm
... ↔ map (j ∘ ↿F) (p ×ᶠ ⊤) ≤ 𝓤 β : by rw map_map
... ↔ ∀ V ∈ 𝓤 β, {x | (c, ↿F x) ∈ V} ∈ (p ×ᶠ ⊤ : filter $ ι × α) : iff.rfl
... ↔ ∀ V ∈ 𝓤 β, {i | ∀ a, (c, F i a) ∈ V} ∈ p : by simpa [filter.mem_prod_top]

-- can this be shorter?
lemma uniform_continuous_on.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] {x : α} {U : set α} (hU : U ∈ 𝓝 x)
  {f : α → β → γ} (h : uniform_continuous_on ↿f (U.prod univ)) :
  tendsto_uniformly f (f x) (𝓝 x) :=
begin
  intros V hV,
  rw [uniform_continuous_on, uniformity_prod_eq_prod] at h,
  specialize h hV,
  rw [mem_map, mem_inf_iff] at h,
  rcases h with ⟨s, hs, t, ht, hst⟩,
  rw [mem_map, mem_prod_iff] at hs, rcases hs with ⟨u, hu, v, hv, huvs⟩,
  rw [mem_principal] at ht,
  rw [← image_subset_iff] at huvs,
  have hU' := mem_nhds_uniformity_iff_right.mp hU,
  rw [nhds_eq_comap_uniformity, eventually_comap],
  apply eventually_of_mem (inter_mem hu hU'),
  rintro ⟨x', y'⟩ ⟨hxyu, hxyU⟩ y hxy b,
  cases hxy,
  show ((x, b), (y, b)) ∈ (λ p : _ × _, (↿f p.1, ↿f p.2)) ⁻¹' V,
  rw [hst],
  refine ⟨huvs ⟨((x, y), (b, b)), _, rfl⟩, ht _⟩,
  exact ⟨hxyu, refl_mem_uniformity hv⟩,
  refine ⟨⟨mem_of_mem_nhds hU, mem_univ b⟩, ⟨hxyU rfl, mem_univ b⟩⟩
end

lemma uniform_continuous₂.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ]
  {f : α → β → γ} (h : uniform_continuous₂ f) {x : α} : tendsto_uniformly f (f x) (𝓝 x) :=
uniform_continuous_on.tendsto_uniformly univ_mem $
  by rwa [univ_prod_univ, uniform_continuous_on_univ]

local attribute [instance] uniform_space.separation_setoid

lemma is_separated.eq_of_uniform_continuous {α β : Type*} [uniform_space α] [uniform_space β]
  {f : α → β} {x y : α} {s : set β} (hs : is_separated s) (hxs : f x ∈ s) (hys : f y ∈ s)
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
(is_separated_def _).mp hs _ _ hxs hys $ λ _ h', h _ (H h')

lemma is_separated.prod {α β : Type*} [uniform_space α] [uniform_space β] {s : set α} {t : set β}
  (hs : is_separated s) (ht : is_separated t) : is_separated (s.prod t) :=
(is_separated_def _).mpr $ assume x y hx hy H, prod.ext
  (hs.eq_of_uniform_continuous hx.1 hy.1 uniform_continuous_fst H)
  (ht.eq_of_uniform_continuous hx.2 hy.2 uniform_continuous_snd H)

lemma is_separated.mono {α : Type*} [uniform_space α] {s t : set α}
  (hs : is_separated s) (hts : t ⊆ s) : is_separated t :=
λ x y hx hy, hs x y (hts hx) (hts hy)

lemma continuous_on.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] [locally_compact_space α] [compact_space β]
  [separated_space β]
  {f : α → β → γ} {x : α} {U : set α} (hxU : U ∈ 𝓝 x) (hU : is_separated U)
  (h : continuous_on ↿f (U.prod univ)) :
  tendsto_uniformly f (f x) (𝓝 x) :=
begin
  rcases locally_compact_space.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩,
  have : uniform_continuous_on ↿f (K.prod univ),
  { refine is_compact.uniform_continuous_on_of_continuous' (hK.prod compact_univ) _
      (h.mono $ prod_mono hKU subset.rfl),
    exact (hU.mono hKU).prod (is_separated_of_separated_space _) },
  exact this.tendsto_uniformly hxK
end

lemma continuous.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [separated_space α] [locally_compact_space α] [uniform_space β]
  [compact_space β] [separated_space β] [uniform_space γ]
  (f : α → β → γ) (h : continuous ↿f) (x : α) : tendsto_uniformly f (f x) (𝓝 x) :=
h.continuous_on.tendsto_uniformly univ_mem $ is_separated_of_separated_space _

end
