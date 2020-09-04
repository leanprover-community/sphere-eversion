import data.real.pi
import has_uncurry

open set function finite_dimensional real
open_locale topological_space

section floor_fract

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

lemma floor_eq_on_Ico (n : ℤ) : ∀ x ∈ (Ico n (n+1) : set α), (n : α) = floor x :=
λ x ⟨h₀, h₁⟩, by exact_mod_cast (floor_eq_iff.mpr ⟨h₀, h₁⟩).symm

lemma continuous_on_floor [topological_space α] (n : ℤ) : 
  continuous_on (λ x, floor x : α → α) (Ico n (n+1) : set α) :=
(continuous_on_congr $ floor_eq_on_Ico n).mp continuous_on_const

lemma tendsto_floor_right' [topological_space α] [order_closed_topology α] (n : ℤ) : 
  filter.tendsto (λ x, floor x : α → α) (𝓝[Ici n] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : α)),
  convert ← (continuous_on_floor _ _ (left_mem_Ico.mpr $ lt_add_one (_ : α))).tendsto,
  rw floor_eq_iff,
  exact ⟨le_refl _, lt_add_one _⟩
end

lemma tendsto_floor_right [topological_space α] [order_closed_topology α] (n : ℤ) : 
  filter.tendsto (λ x, floor x : α → α) (𝓝[Ici n] n) (𝓝[Ici n] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _) 
begin
  refine (eventually_nhds_with_of_forall $ λ x (hx : ↑n ≤ x), _),
  change ↑n ≤ _,
  norm_cast,
  convert ← floor_mono hx,
  rw floor_eq_iff,
  exact ⟨le_refl _, lt_add_one _⟩
end

lemma tendsto_floor_left [topological_space α] [order_closed_topology α] (n : ℤ) :
  filter.tendsto (λ x, floor x : α → α) (𝓝[Iio n] n) (𝓝[Iic (n-1)] (n-1)) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : α)),
  convert (tendsto_nhds_within_congr $ floor_eq_on_Ico (n-1)) 
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds 
      (filter.eventually_of_forall (λ _, mem_Iic.mpr $ le_refl _)));
  norm_cast,
  ring
end

lemma tendsto_floor_left' [topological_space α] [order_closed_topology α] (n : ℤ) :
  filter.tendsto (λ x, floor x : α → α) (𝓝[Iio n] n) (𝓝 (n-1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n),
end

lemma continuous_on_fract [topological_space α] [topological_add_group α] (n : ℤ) : 
  continuous_on (fract : α → α) (Ico n (n+1) : set α) :=
continuous_on_id.sub (continuous_on_floor n)

lemma tendsto_fract_left' [topological_space α] [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : filter.tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝 1) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds filter.tendsto_id).sub (tendsto_floor_left' n);
  [{norm_cast, ring}, apply_instance, apply_instance]
end

lemma tendsto_fract_left [topological_space α] [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : filter.tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝[Iio 1] 1) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ 
  (tendsto_fract_left' _) (filter.eventually_of_forall fract_lt_one)

lemma tendsto_fract_right' [topological_space α] [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : filter.tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝 0) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds filter.tendsto_id).sub (tendsto_floor_right' n);
  [exact (sub_self _).symm, apply_instance, apply_instance]
end

lemma tendsto_fract_right [topological_space α] [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : filter.tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝[Ici 0] 0) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _) (filter.eventually_of_forall fract_nonneg)

local notation `I` := (Icc 0 1 : set α)

lemma continuous_on.comp_fract {β : Type*} [topological_space α] [order_topology α]
  [topological_add_group α] [topological_space β] {f : α → β} 
  (h : continuous_on f I) (hf : f 0 = f 1) : continuous (f ∘ fract) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  by_cases hx : x = floor x,
  { rw [hx,continuous_at_iff_continuous_left'_right', 
        ← continuous_within_at_Ioo_iff_Ioi (lt_add_one (floor x : α))],
    split,
    { simp only [continuous_within_at, hf, fract_coe, comp_app],
      refine filter.tendsto.comp _ (tendsto_fract_left _), 
      rw ← nhds_within_Ioo_eq_nhds_within_Iio (@zero_lt_one α _),
      exact tendsto_nhds_within_mono_left (Ioo_subset_Icc_self) (h 1 ⟨zero_le_one, le_refl _⟩) },
    { exact (h (fract _) ⟨fract_nonneg _, (fract_lt_one _).le⟩).comp 
        ((continuous_on_fract _ _ (left_mem_Ico.mpr $ lt_add_one (_ : α))).mono Ioo_subset_Ico_self) 
        (λ x hx, ⟨fract_nonneg _, (fract_lt_one _).le⟩) } },
  { have : x ∈ Ioo (floor x : α) ((floor x : α) + 1),
      from ⟨lt_of_le_of_ne (floor_le x) (ne.symm hx), lt_floor_add_one _⟩,
    exact ((h _ ⟨fract_nonneg _, (fract_lt_one _).le⟩).comp 
              ((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono Ioo_subset_Ico_self)
              (λ x hx, ⟨fract_nonneg _, (fract_lt_one _).le⟩)).continuous_at 
            (Ioo_mem_nhds this.1 this.2) }
end

lemma continuous_on.comp_fract' {β γ : Type*} [topological_space α] [order_topology α] 
  [topological_add_group α] [topological_space β] [topological_space γ] {f : β → α → γ}
  (h : continuous_on ↿f $ (univ : set β).prod I) (hf : ∀ s, f s 0 = f s 1) : continuous (λ st : β × α, f st.1 $ fract st.2) :=
begin
  change continuous ((↿f) ∘ (prod.map id (fract))),
  rw continuous_iff_continuous_at,
  rintro ⟨s, t⟩,
  by_cases ht : t = floor t,
  { rw ht,
    rw ← continuous_within_at_univ,
    have : (univ : set (β × α)) ⊆ (set.prod univ (Iio $ floor t)) ∪ (set.prod univ (Ici $ floor t)),
    { rintros p -,
      rw ← prod_union,
      exact ⟨true.intro, lt_or_le _ _⟩ },
    refine continuous_within_at.mono _ this,
    refine continuous_within_at.union _ _,
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq, 
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      have : ↿f (s, 0) = ↿f (s, (1 : α)),
        by simp [has_uncurry.uncurry, hf],
      rw this,
      refine (h _ ⟨true.intro, by exact_mod_cast right_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ],
      rw nhds_within_Icc_eq_nhds_within_Iic (@zero_lt_one α _),
      exact filter.tendsto_id.prod_map 
        (tendsto_nhds_within_mono_right Iio_subset_Iic_self $ tendsto_fract_left _) },
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq,
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      refine (h _ ⟨true.intro, by exact_mod_cast left_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ, nhds_within_Icc_eq_nhds_within_Ici (@zero_lt_one α _)],
      exact filter.tendsto_id.prod_map (tendsto_fract_right _) } },
  { have : t ∈ Ioo (floor t : α) ((floor t : α) + 1),
      from ⟨lt_of_le_of_ne (floor_le t) (ne.symm ht), lt_floor_add_one _⟩,
    refine (h ((prod.map _ fract) _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).tendsto.comp _,
    simp only [nhds_prod_eq, nhds_within_prod_eq, nhds_within_univ, id.def, prod.map_mk],
    exact continuous_at_id.tendsto.prod_map 
            (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ 
              (((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono 
                  Ioo_subset_Ico_self).continuous_at (Ioo_mem_nhds this.1 this.2)) 
              (filter.eventually_of_forall (λ x, ⟨fract_nonneg _, (fract_lt_one _).le⟩)) ) }
end

end floor_fract