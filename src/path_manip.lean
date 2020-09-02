import topology.path_connected
import to_mathlib

open set function real
open_locale topological_space

notation `I` := (Icc 0 1 : set ℝ)

@[ext] protected lemma path.ext {X : Type*} [topological_space X] {x y : X} : ∀ {γ₁ γ₂ : path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂
| ⟨x, h11, h12, h13⟩ ⟨.(x), h21, h22, h23⟩ rfl := rfl

/-- Any function `φ : α → path F` can be seen as a function `α × I → F`. -/
instance has_uncurry_path {X α : Type*} [topological_space X] {x y : α → X} : 
has_uncurry (Π (a : α), path (x a) (y a)) (α × I) X := ⟨λ φ p, φ p.1 p.2⟩

lemma path.extend_extends {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ∈ (Icc 0 1 : set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
I_extend_extends γ.to_fun ht

lemma path.extend_extends' {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : (Icc 0 1 : set ℝ)) : γ.extend ↑t = γ t :=
by {convert γ.extend_extends t.2, rw subtype.ext_iff_val}

lemma path.extend_range {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : range γ.extend = range γ :=
I_extend_range γ.to_fun 

lemma path.refl_range {X : Type*} [topological_space X] {a : X} :
  range (path.refl a) = {a} :=
by simp [path.refl, has_coe_to_fun.coe, coe_fn]

lemma path.symm_range {X : Type*} [topological_space X] {a b : X} (γ : path a b) :
  range γ.symm = range γ :=
begin
  ext x,
  simp only [ mem_range, path.symm, has_coe_to_fun.coe, coe_fn, I_symm, set_coe.exists, comp_app, 
              subtype.coe_mk, subtype.val_eq_coe ],
  split; rintros ⟨y, hy, hxy⟩; refine ⟨1-y, Icc_zero_one_symm.mp hy, _⟩; convert hxy,
  exact sub_sub_cancel _ _
end

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

lemma path.extend_le_zero {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ≤ 0) : γ.extend t = a :=
begin
  have := γ.source,
  simpa [path.extend, I_extend, proj_I, ht]
end

lemma path.extend_one_le {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : 1 ≤ t) : γ.extend t = b :=
begin
  simp only [path.extend, I_extend, proj_I, comp_app],
  split_ifs,
  { exfalso, linarith },
  { convert γ.target, linarith },
  { exact γ.target }
end

@[simp] lemma path.refl_symm {X : Type*} [topological_space X] {a : X} :
  (path.refl a).symm = path.refl a :=
begin
  ext,
  refl
end

@[simp] lemma path.refl_extend {X : Type*} [topological_space X] {a : X} :
  (path.refl a).extend = λ _, a := rfl

@[simp] lemma path.refl_trans_refl {X : Type*} [topological_space X] {a : X} :
  (path.refl a).trans (path.refl a) = path.refl a :=
begin
  ext,
  simp only [path.trans, if_t_t, one_div, path.refl_extend],
  refl
end

@[simp] lemma path.symm_cast {X : Type*} [topological_space X] {a₁ a₂ b₁ b₂ : X} 
  (γ : path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) : 
  (γ.cast ha hb).symm = (γ.symm).cast hb ha := rfl

@[simp] lemma path.trans_cast {X : Type*} [topological_space X] {a₁ a₂ b₁ b₂ c₁ c₂ : X} 
  (γ : path a₂ b₂) (γ' : path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) : 
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

noncomputable
def path.portion {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : ℝ) : path a (γ.extend t) :=
{ to_fun := λ s, γ.extend (min s t),
  continuous' := γ.continuous_extend.comp (continuous_subtype_coe.min continuous_const),
  source' := γ.extend_le_zero (min_le_left _ _),
  target' := 
  begin 
    unfold min,
    split_ifs,
    { simp [γ.extend_one_le h] },
    { refl }
  end }

lemma path.portion_range {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} : range (γ.portion t) ⊆ range γ :=
begin
  rw ← γ.extend_range,
  simp only [range_subset_iff, set_coe.exists, set_coe.forall],
  intros x hx,
  simp only [has_coe_to_fun.coe, coe_fn, path.portion, mem_range_self]
end

lemma path.portion_continuous_family {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : continuous ↿(γ.portion) :=
begin
  simp only [has_uncurry.uncurry, has_coe_to_fun.coe, coe_fn, path.portion],
  exact γ.continuous_extend.comp ((continuous_subtype_coe.comp continuous_snd).min continuous_fst),
end

@[simp] lemma path.portion_zero {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : γ.portion 0 = (path.refl a).cast rfl γ.extend_zero :=
begin
  ext x,
  rw path.cast_coe,
  simp [path.portion, has_coe_to_fun.coe, coe_fn, path.refl, γ.extend_le_zero (min_le_right x 0)]
end

@[simp] lemma path.portion_one {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : γ.portion 1 = γ.cast rfl γ.extend_one :=
begin
  ext x,
  rw path.cast_coe,
  simp only [min, path.portion, has_coe_to_fun.coe, coe_fn, path.extend, I_extend, comp_app],
  congr,
  have : ↑x ∈ (Icc 0 1 : set ℝ) := x.2,
  simp [this.2, proj_I_I this]
end

lemma path.symm_continuous_family {X : Type*} [topological_space X] {a b : ℝ → X}
  (γ : Π (t : ℝ), path (a t) (b t)) (h : continuous ↿γ) :
  continuous ↿(λ t, (γ t).symm) :=
h.comp (continuous_id.prod_map continuous_I_symm)

lemma path.continuous_uncurry_extend_of_continuous_family {X : Type*} [topological_space X] 
  {a b : ℝ → X}  (γ : Π (t : ℝ), path (a t) (b t)) (h : continuous ↿γ) :
  continuous ↿(λ t, (γ t).extend) :=
h.comp (continuous_id.prod_map continuous_proj_I)

lemma path.trans_continuous_family {X : Type*} [topological_space X] {a b c : ℝ → X}
  (γ₁ : Π (t : ℝ), path (a t) (b t)) (h₁ : continuous ↿γ₁)
  (γ₂ : Π (t : ℝ), path (b t) (c t)) (h₂ : continuous ↿γ₂) :
  continuous ↿(λ t, (γ₁ t).trans (γ₂ t)) :=
begin
  have h₁' := path.continuous_uncurry_extend_of_continuous_family γ₁ h₁,
  have h₂' := path.continuous_uncurry_extend_of_continuous_family γ₂ h₂,
  simp [has_uncurry.uncurry, has_coe_to_fun.coe, coe_fn, path.trans],
  apply continuous_if _ _ _,
  { rintros ⟨s, t⟩ hst,
    have := frontier_le_subset_eq (continuous_subtype_coe.comp continuous_snd) 
      continuous_const hst,
    simp only [mem_set_of_eq, comp_app] at this,
    simp [this, mul_inv_cancel (@two_ne_zero ℝ _)] },
  { change continuous ((λ p : ℝ × ℝ, (γ₁ p.1).extend p.2) ∘ (prod.map id (λ x, 2*x : I → ℝ))),
    exact h₁'.comp (continuous_id.prod_map $ continuous_const.mul continuous_subtype_coe) },
  { change continuous ((λ p : ℝ × ℝ, (γ₂ p.1).extend p.2) ∘ (prod.map id (λ x, 2*x - 1 : I → ℝ))),
    exact h₂'.comp (continuous_id.prod_map $ 
      (continuous_const.mul continuous_subtype_coe).sub continuous_const) },
end
