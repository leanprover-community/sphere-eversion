import analysis.normed_space.finite_dimension
import analysis.calculus.times_cont_diff
import measure_theory.set_integral
import to_mathlib
import path_manip

import has_uncurry

/-!
# Basic definitions and properties of loops
-/

open set function finite_dimensional
open_locale big_operators topological_space

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

@[ext] protected lemma ext : ∀ {γ₁ γ₂ : loop F}, (γ₁ : ℝ → F) = γ₂ → γ₁ = γ₂
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop F) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

/-- The average value of a loop. -/
noncomputable
def average [measurable_space F] [borel_space F] (γ : loop F) : F := ∫ x in Icc 0 1, (γ x)

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

lemma of_path_continuous {x : F} (γ : path x x) : continuous (of_path γ) :=
begin
  simp only [has_coe_to_fun.coe, coe_fn, of_path],
  apply γ.continuous_extend.continuous_on.comp_fract,
  rw [γ.extend_zero, γ.extend_one]
end

lemma of_path_continuous_family {x : F} (γ : ℝ → path x x) (h : continuous ↿γ) : 
  continuous ↿(λ s, of_path $ γ s) :=
begin
  simp only [of_path, has_uncurry.uncurry, has_coe_to_fun.coe, coe_fn],
  suffices key : continuous (λ (p : ℝ × ℝ), γ p.fst ⟨fract p.snd, _⟩),
  { convert key,
    ext p,
    exact (γ p.fst).extend_extends ⟨fract_nonneg p.snd, (fract_lt_one p.snd).le⟩ },
  change continuous ((λ (p : ℝ × I), γ p.1 p.2) ∘ (λ (p : ℝ × ℝ), ⟨p.1, ⟨fract p.2, _⟩⟩)),
  sorry,

  -- This seems trivial but I'm struggling :(
end

noncomputable
def round_trip {x y : F} (γ : path x y) : loop F :=
of_path (γ.trans γ.symm)

lemma round_trip_range {x y : F} {γ : path x y} : range (round_trip γ) = range γ :=
by simp [round_trip, of_path_range, path.trans_range, path.symm_range]

lemma round_trip_based_at {x y : F} {γ : path x y} : round_trip γ 0 = x :=
begin
  unfold_coes, 
  rw [round_trip, of_path], 
  simp [fract_zero]
end

lemma round_trip_continuous {x y : F} (γ : path x y) : continuous (round_trip γ) :=
of_path_continuous _

noncomputable
def round_trip_family {x y : F} (γ : path x y) : ℝ → loop F :=
λ t, round_trip (γ.portion t)

lemma round_trip_family_continuous {x y : F} {γ : path x y} : continuous ↿(round_trip_family γ) :=
of_path_continuous_family _ 
  (path.trans_continuous_family _ γ.portion_continuous_family _ $
    path.symm_continuous_family _ γ.portion_continuous_family)

lemma round_trip_family_based_at {x y : F} {γ : path x y} : ∀ t, (round_trip_family γ) t 0 = x :=
λ t, round_trip_based_at

lemma round_trip_family_zero {x y : F} {γ : path x y} : (round_trip_family γ) 0 = of_path (path.refl x) :=
begin
  simp only [round_trip_family, round_trip, path.portion_zero, of_path],
  ext z,
  congr,
  ext t,
  simp [path.refl_symm]
end

lemma round_trip_family_one {x y : F} {γ : path x y} : (round_trip_family γ) 1 = round_trip γ :=
begin
  simp only [round_trip_family, round_trip, path.portion_one],
  refl
end

end loop
