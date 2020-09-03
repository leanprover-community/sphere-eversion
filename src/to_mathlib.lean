import data.real.pi
import has_uncurry

open set function finite_dimensional real
open_locale topological_space

lemma real.exists_cos_eq : (Icc (-1) 1 : set ℝ) ⊆ real.cos '' Icc 0 (real.pi) :=
by convert intermediate_value_Icc' (le_of_lt real.pi_pos)
  real.continuous_cos.continuous_on; simp only [real.cos_pi, real.cos_zero]

lemma real.cos_range : range cos = (Icc (-1) 1 : set ℝ) :=
begin
  ext,
  split,
  { rintros ⟨y, hxy⟩,
    exact hxy ▸ ⟨y.neg_one_le_cos, y.cos_le_one⟩ },
  { rintros h,
    rcases real.exists_cos_eq h with ⟨y, _, hy⟩,
    exact ⟨y, hy⟩ }
end

lemma real.sin_range : range sin = (Icc (-1) 1 : set ℝ) :=
begin
  ext,
  split,
  { rintros ⟨y, hxy⟩,
    exact hxy ▸ ⟨y.neg_one_le_sin, y.sin_le_one⟩ },
  { rintros h,
    rcases real.exists_sin_eq h with ⟨y, _, hy⟩,
    exact ⟨y, hy⟩ }
end

lemma floor_eq_on_Ico (n : ℤ) : ∀ x ∈ (Ico n (n+1) : set ℝ), (n : ℝ) = floor x :=
λ x ⟨h₀, h₁⟩, by exact_mod_cast (floor_eq_iff.mpr ⟨h₀, h₁⟩).symm

lemma continuous_on_floor (n : ℤ) : continuous_on (λ x, floor x : ℝ → ℝ) (Ico n (n+1) : set ℝ) :=
(continuous_on_congr $ floor_eq_on_Ico n).mp continuous_on_const

lemma tendsto_floor_right' (n : ℤ) : filter.tendsto (λ x, floor x : ℝ → ℝ) (𝓝[Ici n] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : ℝ)),
  convert ← (continuous_on_floor _ _ (left_mem_Ico.mpr $ lt_add_one _)).tendsto,
  rw floor_eq_iff,
  split; linarith
end

lemma tendsto_floor_right (n : ℤ) : filter.tendsto (λ x, floor x : ℝ → ℝ) (𝓝[Ici n] n) (𝓝[Ici n] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _) 
begin
  refine (eventually_nhds_with_of_forall $ λ x (hx : ↑n ≤ x), _),
  change ↑n ≤ _,
  norm_cast,
  convert ← floor_mono hx,
  rw floor_eq_iff,
  split; linarith
end

lemma tendsto_floor_left (n : ℤ) : filter.tendsto (λ x, floor x : ℝ → ℝ) (𝓝[Iio n] n) (𝓝[Iic (n-1)] (n-1)) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : ℝ)),
  convert (tendsto_nhds_within_congr $ floor_eq_on_Ico (n-1)) 
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds 
      (filter.eventually_of_forall (λ _, mem_Iic.mpr $ le_refl _)));
  norm_cast,
  ring
end

lemma tendsto_floor_left' (n : ℤ) : filter.tendsto (λ x, floor x : ℝ → ℝ) (𝓝[Iio n] n) (𝓝 (n-1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n),
end

lemma continuous_on_fract (n : ℤ) : continuous_on (fract : ℝ → ℝ) (Ico n (n+1) : set ℝ) :=
continuous_on_id.sub (continuous_on_floor n)

lemma tendsto_fract_left' (n : ℤ) : filter.tendsto (fract : ℝ → ℝ) (𝓝[Iio n] n) (𝓝 1) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds filter.tendsto_id).sub (tendsto_floor_left' n),
  norm_cast,
  ring
end

lemma tendsto_fract_left (n : ℤ) : filter.tendsto (fract : ℝ → ℝ) (𝓝[Iio n] n) (𝓝[Iio 1] 1) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _) (filter.eventually_of_forall fract_lt_one)

lemma tendsto_fract_right' (n : ℤ) : filter.tendsto (fract : ℝ → ℝ) (𝓝[Ici n] n) (𝓝 0) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds filter.tendsto_id).sub (tendsto_floor_right' n),
  ring
end

lemma tendsto_fract_right (n : ℤ) : filter.tendsto (fract : ℝ → ℝ) (𝓝[Ici n] n) (𝓝[Ici 0] 0) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _) (filter.eventually_of_forall fract_nonneg)

lemma continuous_on.comp_fract {α : Type*} [topological_space α] {f : ℝ → α} 
  (h : continuous_on f (Icc 0 1)) (hf : f 0 = f 1) : continuous (f ∘ fract) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  by_cases hx : x = floor x,
  { rw [hx,continuous_at_iff_continuous_left'_right', 
        ← continuous_within_at_Ioo_iff_Ioi (lt_add_one (floor x : ℝ))],
    split,
    { simp only [continuous_within_at, hf, fract_coe, comp_app],
      refine filter.tendsto.comp _ (tendsto_fract_left _), 
      rw ← nhds_within_Ioo_eq_nhds_within_Iio real.zero_lt_one,
      exact tendsto_nhds_within_mono_left (Ioo_subset_Icc_self) (h 1 ⟨zero_le_one, le_refl _⟩) },
    { exact (h (fract _) ⟨fract_nonneg _, (fract_lt_one _).le⟩).comp 
        ((continuous_on_fract _ _ (left_mem_Ico.mpr $ lt_add_one _)).mono Ioo_subset_Ico_self) 
        (λ x hx, ⟨fract_nonneg _, (fract_lt_one _).le⟩) } },
  { have : x ∈ Ioo (floor x : ℝ) ((floor x : ℝ) + 1),
      from ⟨lt_of_le_of_ne (floor_le x) (ne.symm hx), lt_floor_add_one _⟩,
    exact ((h _ ⟨fract_nonneg _, (fract_lt_one _).le⟩).comp 
              ((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono Ioo_subset_Ico_self)
              (λ x hx, ⟨fract_nonneg _, (fract_lt_one _).le⟩)).continuous_at 
            (Ioo_mem_nhds this.1 this.2) }
end