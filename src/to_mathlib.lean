import data.real.pi

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

lemma path.extend_extends {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ∈ (Icc 0 1 : set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
I_extend_extends γ.to_fun ht

lemma path.extend_extends' {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : (Icc 0 1 : set ℝ)) : γ.extend ↑t = γ t :=
by {convert γ.extend_extends t.2, rw subtype.ext_iff_val}

lemma path.extend_range {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : range γ.extend = range γ :=
I_extend_range γ.to_fun 

lemma path.trans_range {X : Type*} [topological_space X] {a b c : X}
  (γ₁ : path a b) (γ₂ : path b c) : range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ :=
begin
  rw path.trans,
  apply eq_of_subset_of_subset,
  { rintros x ⟨⟨t, ht0, ht1⟩, hxt⟩,
    by_cases h : t ≤ 1/2,
    { left,
      use [2*t, ⟨by linarith, by linarith⟩],
      rw ← γ₁.extend_extends,
      unfold_coes at hxt,
      simp only [h, comp_app, if_true] at hxt,
      exact hxt },
    { right,
      use [2*t-1, ⟨by linarith, by linarith⟩],
      rw ← γ₂.extend_extends,
      unfold_coes at hxt,
      simp only [h, comp_app, if_false] at hxt,
      exact hxt } },
  { rintros x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩),
    { use ⟨t/2, ⟨by linarith, by linarith⟩⟩,
      unfold_coes,
      have : t/2 ≤ 1/2 := by linarith,
      simp only [this, comp_app, if_true],
      ring,
      rwa γ₁.extend_extends },
    { by_cases h : t = 0,
      { use ⟨1/2, ⟨by linarith, by linarith⟩⟩,
        unfold_coes,
        simp only [h, comp_app, if_true, le_refl, mul_one_div_cancel (@two_ne_zero ℝ _)],
        rw γ₁.extend_one,
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt },
      { use ⟨(t+1)/2, ⟨by linarith, by linarith⟩⟩,
        unfold_coes,
        change t ≠ 0 at h,
        have ht0 := lt_of_le_of_ne ht0 h.symm,
        have : ¬ (t+1)/2 ≤ 1/2 := by {rw not_le, linarith},
        simp only [comp_app, if_false, this],
        ring,
        rwa γ₂.extend_extends } } }
end

private lemma exists_path_through_family_aux
  {X : Type*} [topological_space X] {s : set X} (h : is_path_connected s) (n : ℕ)
  (p : ℕ → X) (hp : ∀ i ≤ n, p i ∈ s) : ∃ γ : path (p 0) (p n), (∀ i ≤ n, p i ∈ range γ) ∧ (range γ ⊆ s) :=
begin
  induction n with n hn,
  { use (λ _, p 0),
    { continuity },
    { split,
      { rintros i hi, rw nat.le_zero_iff.mp hi, exact ⟨0, rfl⟩ },
      { rw range_subset_iff, rintros x, exact hp 0 (le_refl _) } } },
  { rcases hn (λ i hi, hp i $ nat.le_succ_of_le hi) with ⟨γ₀, hγ₀⟩,
    rcases h.joined_in (p n) (p $ n+1) (hp n n.le_succ) (hp (n+1) $ le_refl _) with ⟨γ₁, hγ₁⟩,
    let γ : path (p 0) (p $ n+1) := γ₀.trans γ₁,
    use γ,
    have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁,
    split, 
    { rintros i hi,
      by_cases hi' : i ≤ n,
      { rw range_eq,  
        left,
        exact hγ₀.1 i hi' },
      { rw [not_le, ← nat.succ_le_iff] at hi',
        have : i = n.succ := by linarith,
        rw this,
        use 1,
        exact γ.target } },
    { rw range_eq,
      apply union_subset hγ₀.2,
      rw range_subset_iff,
      exact hγ₁ } }
end

lemma is_path_connected.exists_path_through_family
  {X : Type*} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s) 
  (p : fin (n+1) → X) (hp : ∀ i, p i ∈ s) : ∃ γ : path (p 0) (p n), (∀ i, p i ∈ range γ) ∧ (range γ ⊆ s) :=
begin
  let p' : ℕ → X := λ k, if h : k < n+1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩,
  have hpp' : ∀ k < n+1, p k = p' k,
  { intros k hk, simp only [p', hk, dif_pos], congr, ext, rw fin.coe_val_of_lt hk },
  have := exists_path_through_family_aux h n p'
  begin
    intros i hi,
    simp [p', nat.lt_succ_of_le hi, hp]
  end,
  rcases this with ⟨γ, hγ⟩,
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self),
  simp only [γ.cast_coe],
  refine and.intro _ hγ.2,
  rintros ⟨i, hi⟩,
  convert hγ.1 i (nat.le_of_lt_succ hi), rw ← hpp' i hi,
  congr,
  ext,
  rw fin.coe_val_of_lt hi
end

notation `I` := (Icc 0 1 : set ℝ)

lemma is_path_connected.exists_path_through_family'
  {X : Type*} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s) 
  (p : fin (n+1) → X) (hp : ∀ i, p i ∈ s) :
  ∃ (γ : path (p 0) (p n)) (t : fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i :=
begin
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩,
  rcases hγ with ⟨h₁, h₂⟩,
  simp only [range, mem_set_of_eq] at h₁,
  rw range_subset_iff at h₂,
  choose! t ht using h₁,
  exact ⟨γ, t, h₂, ht⟩
end