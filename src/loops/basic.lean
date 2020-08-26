import analysis.normed_space.finite_dimension
import analysis.calculus.times_cont_diff
import measure_theory.set_integral

import has_uncurry

/-!
# Basic definitions and properties of loops
-/

open set function finite_dimensional
open_locale big_operators topological_space

lemma path.extend_extends {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : γ.extend t = γ ⟨t, ht⟩ :=
I_extend_extends γ.to_fun ht

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

lemma is_path_connected.exists_path_through_family'
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
    rcases h.joined_in (p n) (p n.succ) (hp n n.le_succ) (hp n.succ $ le_refl _) with ⟨γ₁, hγ₁⟩,
    let γ : path (p 0) (p n.succ) := γ₀.trans γ₁,
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
  (p : fin n.succ → X) (hp : ∀ i, p i ∈ s) : ∃ γ : path (p 0) (p n), (∀ i, p i ∈ range γ) ∧ (range γ ⊆ s) :=
begin
  let p' : ℕ → X := λ k, if h : k < n.succ then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩,
  have hpp' : ∀ k < n.succ, p k = p' k,
  { intros k hk, simp only [p', hk, dif_pos], congr, ext, rw fin.coe_val_of_lt hk },
  have := h.exists_path_through_family' n p'
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


def nhds_set {α : Type*} [topological_space α] (s : set α) : filter α :=
Sup (nhds '' s)

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]

local notation `d` := findim ℝ F

local notation `smooth_on` := times_cont_diff_on ℝ ⊤

def smooth_at (f : E → F) (x : E) : Prop := ∃ s ∈ 𝓝 x, smooth_on f s

section surrounding_points

def affinely_independent {n : ℕ} (p : fin n → F) : Prop :=
sorry

-- def:surrounds_points
structure surrounding_pts (f : F) (p : fin (d + 1) → F) (w : fin (d + 1) → ℝ) : Prop :=
(indep : affinely_independent p)
(w_pos : ∀ i, 0 < w i)
(w_sum : ∑ i, w i = 1)
(avg : ∑ i, (w i) • (p i) = f)


def surrounded (f : F) (s : set F) : Prop :=
∃ p w, surrounding_pts f p w ∧ ∀ i, p i ∈ s

-- lem:int_cvx alternative formulation, compare int_cvx.lean
lemma surrounded_of_convex_hull {f : F} {s : set F} (hs : is_open s) (hsf : f ∈ convex_hull s) : surrounded f s :=
sorry

-- lem:smooth_convex_hull
lemma smooth_surrounding {x : F} {p w} (h : surrounding_pts x p w) : 
  ∃ w : F → (fin (d+1) → F) → (fin (d+1) → ℝ),
  ∀ᶠ y in 𝓝 x, ∀ᶠ q in  𝓝 p, smooth_at (uncurry w) (y, q) ∧ 
                              ∀ i, w y q i ∈ Ioo (0 : ℝ) 1 ∧ 
                              ∑ i, w y q i • q i = y :=
sorry

end surrounding_points

set_option old_structure_cmd true

variables (E F)

structure loop :=
(to_fun : ℝ → F)
(per' : ∀ t, to_fun (t + 1) = to_fun t)

instance : has_coe_to_fun (loop F) := ⟨_, λ γ, γ.to_fun⟩

/-- Any function `φ : α → loop F` can be seen as a function `α × ℝ → F`. -/
instance has_uncurry_loop {α : Type*} : has_uncurry (α → loop F) (α × ℝ) F := ⟨λ φ p, φ p.1 p.2⟩

variables {E F}

namespace loop

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop F) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

/-- The average value of a loop. -/
noncomputable
def average [measurable_space F] [borel_space F] (γ : loop F) : F := ∫ x in Icc 0 1, (γ x)

#check fract_nonneg

noncomputable
def of_path {x : F} (γ : path x x) : loop F :=
{ to_fun := λ t, γ.extend (fract t),
  per' := 
  begin
    intros t,
    congr' 1,
    rw fract_eq_fract,
    use 1,
    norm_num
  end }

#check subtype.ext_iff

lemma of_path_range {x : F} (γ : path x x) : range (of_path γ) = range γ :=
begin
  apply eq_of_subset_of_subset; rw range_subset_iff,
  { intro t,
    rw ← γ.extend_range,
    exact ⟨fract t, rfl⟩ },
  { rintro t,
    by_cases ht1 : t = 1,
    { rw [ht1, of_path],
      use 0,
      unfold_coes,
      simp [path.target'], },
    { use t,
      rw subtype.ext_iff at ht1,
      change (t : ℝ) ≠ 1 at ht1,
      have : fract t.val = t.val,
      { rw fract_eq_iff,
        exact ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1, ⟨0, sub_self _⟩⟩ },
      rw of_path,
      unfold_coes,
      simp only [this, γ.extend_extends t.2],
      congr',
      rw subtype.ext_iff_val } }
end 

end loop
