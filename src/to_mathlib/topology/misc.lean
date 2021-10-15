import topology.path_connected

noncomputable theory

open set function filter
open_locale unit_interval topological_space uniformity filter

section -- to bounded_lattice

variables {α β : Type*}

lemma function.surjective.map_top {f : α → β} (hf : surjective f) : filter.map f ⊤ = ⊤ :=
begin
  ext, simp only [mem_map, mem_top, eq_univ_iff_forall, mem_preimage],
  exact (@surjective.forall _ _ _ hf (∈ s)).symm,
end

end

section -- to topology.algebra.ordered.proj_Icc

variables {α β γ : Type*} [linear_order α]
  [topological_space β] [topological_space γ] {a b c : α} {h : a ≤ b}

lemma filter.tendsto.Icc_extend (f : γ → Icc a b → β) {z : γ} {l : filter α} {l' : filter β}
  (hf : tendsto ↿f (𝓝 z ×ᶠ l.map (proj_Icc a b h)) l') :
  tendsto ↿(Icc_extend h ∘ f) (𝓝 z ×ᶠ l) l' :=
show tendsto (↿f ∘ prod.map id (proj_Icc a b h)) (𝓝 z ×ᶠ l) l', from
hf.comp $ tendsto_id.prod_map tendsto_map

variables [topological_space α] [order_topology α]

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

lemma continuous.extend'{γ : Y → path x y} (hγ : continuous ↿γ) :
  continuous ↿(λ t, (γ t).extend) :=
continuous.Icc_extend' hγ

lemma filter.tendsto.extend {X Y : Type*} [topological_space X] [topological_space Y] {x₁ x₂ : X}
  {y : Y} {l : filter ℝ} {l' : filter X} {γ : Y → path x₁ x₂}
  (hγ : tendsto ↿γ (𝓝 y ×ᶠ l.map (proj_Icc 0 1 zero_le_one)) l') :
  tendsto ↿(λ t, (γ t).extend) (𝓝 y ×ᶠ l) l' :=
filter.tendsto.Icc_extend _ hγ

lemma continuous.extend  {f : Z → Y} {g : Z → ℝ} {γ : Y → path x y} (hγ : continuous ↿γ)
  (hf : continuous f) (hg : continuous g) :
  continuous (λ i, (γ (f i)).extend (g i)) :=
(continuous.extend' hγ).comp $ hf.prod_mk hg

lemma continuous_at.extend {f : Z → Y} {g : Z → ℝ} {γ : Y → path x y} {z : Z}
  (hγ : continuous_at ↿γ (f z, proj_Icc 0 1 zero_le_one (g z))) (hf : continuous_at f z)
  (hg : continuous_at g z) : continuous_at (λ i, (γ (f i)).extend (g i)) z :=
show continuous_at
  ((λ p : Y × ℝ, (Icc_extend (@zero_le_one ℝ _) (γ p.1) p.2)) ∘ (λ i, (f i, g i))) z, from
continuous_at.comp (continuous_at.Icc_extend (λ x y, γ x y) hγ) $ hf.prod hg

end
section -- to topology.algebra.group_with_zero

variables {α G₀ β γ : Type*} [group_with_zero G₀] [topological_space G₀]
  [has_continuous_inv₀ G₀] [has_continuous_mul G₀]

lemma continuous_at.comp_div_cases  {f g : α → G₀} {k : α → γ} (h : γ → G₀ → β)
  [topological_space α] [topological_space β] [topological_space γ] {a : α} (c : γ)
  (hk : continuous_at k a) (hf : continuous_at f a) (hg : continuous_at g a)
  (hh : g a ≠ 0 → continuous_at ↿h (k a, f a / g a))
  (h2h : filter.tendsto ↿h (𝓝 c ×ᶠ ⊤) (𝓝 (h c 0)))
  (hgk : ∀ {a}, g a = 0 → k a = c) :
  continuous_at (λ x, h (k x) (f x / g x)) a :=
begin
  show continuous_at (↿h ∘ (λ x, (k x, f x / g x))) a,
  by_cases hga : g a = 0,
  { rw [continuous_at], simp_rw [comp_app, hga, div_zero, hgk hga],
    refine h2h.comp _, rw [← hgk hga], exact hk.prod_mk filter.tendsto_top },
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
lemma tendsto_prod_top_iff {α β ι : Type*} [uniform_space β] {F : ι → α → β} {c : β}
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
lemma uniform_continuous₂.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ]
  {f : α → β → γ} (h : uniform_continuous₂ f) {x : α} : tendsto_uniformly f (f x) (𝓝 x) :=
begin
  intros U hU,
  rw [uniform_continuous₂, uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff, (∘)] at h,
  dsimp at h,
  rcases mem_map_iff_exists_image.1 (h hU) with ⟨t, ht, hts⟩, clear h,
  rcases mem_prod_iff.1 ht with ⟨u, hu, v, hv, huvt⟩, clear ht,
  rw [nhds_eq_comap_uniformity, eventually_comap],
  apply eventually_of_mem hu,
  rintro ⟨x', y'⟩ hxyu y hxy b,
  simp_rw [prod.ext_iff] at hxy,
  rcases hxy with ⟨rfl, rfl⟩,
  refine hts ⟨⟨⟨x, y⟩, ⟨b, b⟩⟩, huvt _, rfl⟩,
  exact ⟨hxyu, refl_mem_uniformity hv⟩
end

end
