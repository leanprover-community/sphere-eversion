import analysis.special_functions.pow

import to_mathlib.logic.basic
import to_mathlib.data.nat.basic
import to_mathlib.topology.germ
import to_mathlib.order.filter.basic

import notations
import global.indexing

noncomputable theory

open set filter
open_locale topology

private def T : ℕ → ℝ := λ n, nat.rec 0 (λ k x, x + 1/(2 : ℝ)^(k+1)) n

open_locale big_operators

-- Note this is more painful than Patrick hoped for. Maybe this should be the definition of T.
private lemma T_eq (n : ℕ) : T n = 1- (1/(2: ℝ))^n :=
begin
  have : T n = ∑ k in finset.range n, 1/(2: ℝ)^(k+1),
  { induction n with n hn,
    { simp only [T, finset.range_zero, finset.sum_empty] },
    change T n + _ = _,
    rw [hn, finset.sum_range_succ] },
  simp_rw [this, ← one_div_pow, pow_succ, ← finset.mul_sum, geom_sum_eq (by norm_num : 1/(2:ℝ) ≠ 1) n],
  field_simp,
  norm_num,
  apply div_eq_of_eq_mul,
  apply neg_ne_zero.mpr,
  apply ne_of_gt,
  positivity,
  ring
end

private lemma T_lt (n : ℕ) : T n < 1 :=
begin
  rw T_eq,
  have : (0 : ℝ) < (1 / 2) ^ n, by positivity,
  linarith
end

private lemma T_lt_succ (n : ℕ) : T n < T (n+1) :=
lt_add_of_le_of_pos le_rfl (one_div_pos.mpr (pow_pos zero_lt_two _))

private lemma T_le_succ (n : ℕ) : T n ≤ T (n+1) := (T_lt_succ n).le

private lemma T_succ_sub (n : ℕ) : T (n+1) - T n = 1/2^(n+1) :=
begin
  change T n + _ - T n = _,
  simp
end

private lemma mul_T_succ_sub (n : ℕ) : 2^(n+1)*(T (n+1) - T n) = 1 :=
begin
  rw T_succ_sub,
  field_simp
end

private lemma T_one : T 1 = 1/2 :=
by simp [T]

private lemma not_T_succ_le (n : ℕ) : ¬ T (n + 1) ≤ 0 :=
begin
  rw [T_eq, not_le],
  have : (1 / (2 : ℝ)) ^ (n + 1) < 1,
  apply pow_lt_one ; norm_num,
  linarith,
end

lemma inductive_htpy_construction_aux {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop) (P₂ : Π p : ℝ × X, germ (𝓝 p) Y → Prop)
  (hP₂ : ∀ a b (p : ℝ × X) (f : ℝ × X → Y), P₂ (a*p.1+b, p.2) f → P₂ p (λ p : ℝ × X, f (a*p.1+b, p.2)))
  {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1)) :
  ∃ f : ℕ → ℝ × X → Y, ∀ n,
    ((∀ p : ℝ × X, P₀ p.2 (filter.germ.slice_right (f n)) ∧ P₂ p (f n)) ∧
    (∀ᶠ x near (⋃ i ≤ (n : index_type N) , K i), P₁ x (filter.germ.slice_right (f n : (𝓝 (T (n+1), x)).germ Y))) ∧
    (∀ t ≥ T (n+1), ∀ x, f n (t, x) = f n (T (n+1), x)) ∧ (∀ x, f n (0, x) = f₀ x) ∧
    (∀ᶠ t in 𝓝 (T $ n+1), ∀ x, f n (t, x) = f n (T (n+1), x))) ∧
    (((((n+1:ℕ) : index_type N) = n) → f (n+1) = f n) ∧
      ∀ x ∉ U (n + 1 : ℕ), ∀ t, f (n+1) (t, x) = f n (t, x))
   :=
begin
  let P₀' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₀ p.2 φ.slice_right ∧ P₂ p φ,
  let P₁' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₁ p.2 φ.slice_right,
  let P : ℕ → (ℝ × X → Y) → Prop :=
    λ n f, (∀ p, P₀' p f) ∧ (∀ᶠ x near (⋃ i ≤ (n : index_type N) , K i), P₁' (T (n+1), x) f) ∧
           (∀ t ≥ T (n+1), ∀ x, f (t, x) = f (T (n+1), x)) ∧ (∀ x, f (0, x) = f₀ x) ∧
           (∀ᶠ t in 𝓝 (T $ n+1), ∀ x, f (t, x) = f (T (n+1), x)),
  let Q : ℕ → (ℝ × X → Y) → (ℝ × X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧
              (∀ x ∉ U (n + 1 : ℕ), ∀ t, f' (t, x) = f (t, x)),
  change ∃ f : ℕ → ℝ × X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  apply exists_by_induction',
  { dsimp only [P],
    rcases ind 0 f₀ init _ with ⟨f', h₀f', h₁f', hf'₂, hf'not, hf'0, hf'1⟩,
    refine ⟨λ p, f' (2*p.1) p.2, λ p, ⟨_, _⟩, _, _, _, _⟩,
    { exact h₀f' (2*p.1) p.2 },
    { simpa using hP₂ 2 0 p ↿f' (hf'₂ _) },
    { apply h₁f'.mono,
      intros x hx,
      change P₁ x (λ x' : X, f' (2*T (0 + 1)) x'),
      simpa [T] using hx },
    { simp only [T, zero_add, one_div, nat.rec_add_one, algebra_map.coe_zero, nat.rec_zero,
                  pow_one, real.rpow_one, ge_iff_le, mul_inv_cancel_of_invertible],
      intros t ht x,
      rw ← hf'1.on_set (2*t) _,
      change 1 ≤ 2*t,
      field_simp at ht,
      linarith only [ht] },
    { intros x,
      rw hf'0.on_set,
      simp },
    { dsimp only,
      have : 2 * T (0 + 1) = 1, by simp [T_one],
      rw [this, zero_add],
      have : 𝓝 (1 : ℝ) ≤ 𝓝ˢ (Ici 1),
            { exact nhds_le_nhds_set left_mem_Ici },
      have : f' =ᶠ[𝓝 1] λ t, f' 1 := hf'1.filter_mono this,
      have lim : tendsto (λ t : ℝ, 2*t) (𝓝 $ T 1) (𝓝 1),
      { rw [T_one],
        convert tendsto_id.const_mul (2 : ℝ),
        simp },
      apply (this.comp_fun lim).mono (λ t ht, _),
      intro x',
      apply congr_fun ht },
    { simp [index_type.not_lt_zero] } },
  { rintros n f ⟨h₀'f, h₁f, hinvf, hf0, hfTn1⟩,
    rcases index_type.lt_or_eq_succ N n with hn | hn,
    { simp_rw index_type.le_or_lt_succ hn at h₁f,
      rcases ind (n+1 : ℕ) (λ x, f (T (n+1), x)) (λ x, (h₀'f (T (n+1), x)).1) h₁f with
        ⟨f', h₀f', h₁f', hf'₂, hf'not, hf'0, hf'1⟩,
      refine ⟨λ p, if p.1 ≥ T (n+1) then f' (2^(n+2)*(p.1 - T (n+1))) p.2 else f p, ⟨λ p, ⟨_, _⟩, _, _, _, _⟩, _, _⟩,
      { by_cases ht : (T $ n+1) ≤ p.1,
        { convert h₀f' (2^(n+2)*(p.1-T (n+1))) p.2 using 1,
          apply quotient.sound,
          simp [ht] },
        { convert (h₀'f p).1 using 1,
          apply quotient.sound,
          simp [ht] } },
      { rcases lt_trichotomy (T $ n+1) p.1 with ht|ht|ht,
        { convert hP₂ (2^(n+2)) (-2^(n+2)*T (n+1)) p ↿f' (hf'₂ _) using 1,
          apply quotient.sound,
          have hp : ∀ᶠ (q : ℝ × X) in 𝓝 p, T (n+1) ≤ q.1,
          { cases p with t x,
            apply mem_of_superset (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem),
            rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
            exact le_of_lt ht' },
          apply hp.mono (λ q hq, _),
          simp [if_pos hq, mul_sub, neg_mul],
          refl },
        { let g : ℝ × X → Y := λ p, f' (2 ^ (n + 2) * (p.fst - T (n + 1))) p.snd,
          have hg : P₂ p g,
          { convert hP₂ (2^(n+2)) (-2^(n+2)*T (n+1)) p ↿f' (hf'₂ _) using 2,
            ext q,
            dsimp only [g],
            ring_nf },
          convert hg using 1,
          apply quotient.sound,
          apply filter.eventually_eq.eventually_eq_ite,
          cases p with t x,
          have hf : f =ᶠ[𝓝 (t, x)] λ q : ℝ × X, f (T (n + 1), q.2),
          { change T (n+1) = t at ht,
            rw ← ht,
            apply mem_of_superset (prod_mem_nhds hfTn1 univ_mem),
            rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
            exact ht' x' },
          replace hf'0 : ↿f' =ᶠ[𝓝 (0, x)] λ q : ℝ × X, f (T (n + 1), q.2),
          { have : 𝓝 (0 : ℝ) ≤ 𝓝ˢ (Iic 0),
            { exact nhds_le_nhds_set right_mem_Iic },
            apply mem_of_superset (prod_mem_nhds (hf'0.filter_mono this) univ_mem),
            rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
            exact (congr_fun ht' x' : _) },
          have : tendsto (λ (x : ℝ × X), (2 ^ (n + 2) * (x.1 - T (n + 1)), x.2)) (𝓝 (t, x)) (𝓝 (0, x)),
          { rw [nhds_prod_eq, nhds_prod_eq],
            have limt : tendsto (λ t, 2 ^ (n + 2) * (t - T (n + 1))) (𝓝 t) (𝓝 0),
            { rw [show (0 : ℝ) = 2^(n+2)*(T (n+1) - T (n+1)), by simp, ht],
              apply tendsto.const_mul,
              exact tendsto_id.sub_const _ },
            exact limt.prod_map tendsto_id },
          have := hf'0.comp_fun this,
          rw show (λ (q : ℝ × X), f (T (n + 1), q.2)) ∘
            (λ (x : ℝ × X), (2 ^ (n + 2) * (x.1 - T (n + 1)), x.2)) =
            λ q : ℝ × X, f (T (n + 1), q.2),
          by { ext, refl } at this,
          exact this.trans hf.symm },
        { have hp : ∀ᶠ (q : ℝ × X) in 𝓝 p, ¬ T (n+1) ≤ q.1,
          { cases p with t x,
            apply mem_of_superset (prod_mem_nhds (Iio_mem_nhds ht) univ_mem),
            rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
            simpa using ht' },
          convert (h₀'f p).2 using 1,
          apply quotient.sound,
          apply hp.mono (λ q hq, _),
          simp [if_neg hq] } },
      { apply h₁f'.mono,
        intros x hx,
        change P₁ x (λ x', if T (n+2) ≥ T (n+1) then f' (2^(n+2)*(T (n+2) - T (n+1))) x' else _),
        convert hx using 2,
        ext x',
        simp [if_pos (T_le_succ $ n+1), T_succ_sub] },
      { rintros t ht x,
        dsimp only,
        simp only [if_pos ((T_le_succ $ n+1).trans ht), if_pos (T_le_succ $ n+1),
                    T_succ_sub, one_div, mul_inv_cancel_of_invertible],
        replace ht : 1 / 2 ^ (n + 2) ≤ t - T (n+1) := le_sub_iff_add_le'.mpr ht,
        rw ← hf'1.on_set _ _,
        exact (div_le_iff' (by positivity)).mp ht },
      { intros x,
        simp [not_T_succ_le, hf0] },
      { suffices : (λ t x, f' (2 ^ (n + 2) * (t - T (n + 1))) x) =ᶠ[𝓝 (T (n + 2))] (λ t x, f' (2 ^ (n + 2) * (T (n+2) - T (n + 1))) x),
        { have hle : ∀ᶠ (t : ℝ) in 𝓝 (T (n + 1 + 1)), t ≥ T (n+1),
            from eventually_ge_of_tendsto_gt (T_lt_succ _) tendsto_id,
          apply (hle.and this).mono,
          rintros t ⟨ht, ht'⟩ x,
          dsimp only,
          rw [if_pos ht, if_pos (T_le_succ _)],
          apply congr_fun ht' },
        have : 𝓝 (1 : ℝ) ≤ 𝓝ˢ (Ici 1),
            { exact nhds_le_nhds_set left_mem_Ici },
        rw mul_T_succ_sub,
        have : f' =ᶠ[𝓝 1] λ t, f' 1 := hf'1.filter_mono this,
        apply this.comp_fun,
        conv { congr, congr, skip, rw ← mul_T_succ_sub (n+1) },
        exact (tendsto_id.sub_const _).const_mul _ },
      { exact λ hn', (hn.ne hn'.symm).elim },
      { intros x hx t,
        dsimp only,
        split_ifs with ht,
        { rw [hf'not _ _ hx, hinvf _ ht] },
        { refl }, } },
    { simp only [hn] at h₁f,
      refine ⟨f, ⟨h₀'f, _, _, hf0, _⟩, _, _⟩,
      { apply h₁f.mono,
        intros x hx,
        change P₁ x (λ x, f (T (n+2), x)),
        convert hx using 2,
        ext x',
        apply  hinvf,
        apply T_le_succ },
      { intros t ht x,
        rw [hinvf (T $ n+1+1) (T_le_succ _), hinvf _ ((T_le_succ $ n+1).trans ht)] },
      { have hle : ∀ᶠ (t : ℝ) in 𝓝 (T (n + 1 + 1)), t ≥ T (n+1),
            from eventually_ge_of_tendsto_gt (T_lt_succ _) tendsto_id,
        apply hle.mono (λ t ht, _),
        intro x,
        rw [hinvf t ht, hinvf (T $ n+2) (T_le_succ _)] },
      { simp },
      { simp } } }
end

/- TODO: think whether `∀ x ∈ ⋃ j < i, K j, P₁ x f` should be something more general. -/
lemma inductive_htpy_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop) (P₂ : Π p : ℝ × X, germ (𝓝 p) Y → Prop)
  (hP₂ : ∀ a b (p : ℝ × X) (f : ℝ × X → Y), P₂ (a*p.1+b, p.2) f → P₂ p (λ p : ℝ × X, f (a*p.1+b, p.2)))
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1)) :
  ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ (∀ p, P₂ p ↿F) :=
begin
  let P₀' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₀ p.2 φ.slice_right ∧ P₂ p φ,
  let P₁' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₁ p.2 φ.slice_right,
  let P : ℕ → (ℝ × X → Y) → Prop :=
    λ n f, (∀ p, P₀' p f) ∧ (∀ᶠ x near (⋃ i ≤ (n : index_type N) , K i), P₁' (T (n+1), x) f) ∧
           (∀ t ≥ T (n+1), ∀ x, f (t, x) = f (T (n+1), x)) ∧ (∀ x, f (0, x) = f₀ x) ∧
           (∀ᶠ t in 𝓝 (T $ n+1), ∀ x, f (t, x) = f (T (n+1), x)),
  let Q : ℕ → (ℝ × X → Y) → (ℝ × X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧
              (∀ x ∉ U (n + 1 : ℕ), ∀ t, f' (t, x) = f (t, x)),
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ × X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  { apply inductive_htpy_construction_aux; assumption },
  simp only [P, Q, forall_and_distrib, forall₂_and_distrib] at hf,
  rcases hf with ⟨⟨⟨h₀f, h₂f⟩, h₁f, hinvf, hf0, hfTsucc⟩, hf₁, hf₃⟩,
  choose W W_in hW using U_fin,
  choose i₀ hi₀ using λ x, (hW x).bdd_above,
  have : ∀ x, ∃ n : ℕ, x ∈ K n,
  { intros x,
    rcases eq_univ_iff_forall.mp K_cover x with ⟨-, ⟨i, rfl⟩, hi⟩,
    use indexing.to_nat i,
    simpa using hi },
  choose nK hnK using this,
  let n₀ : X → ℕ := λ x, max (nK x) (indexing.to_nat (i₀ x)),
  have key : ∀ {x : X} {n}, n ≥ n₀ x → ∀ {q : ℝ × X}, q.2 ∈ W x → f n q = f (n₀ x) q,
  { intros x₀ n hn,
    rcases le_iff_exists_add.mp hn with ⟨k, rfl⟩, clear hn,
    rintros ⟨t, x⟩ (hx : x ∈ _),
    induction k with k hk,
    { rw add_zero },
    rw ← hk, clear hk,
    let π :  ℕ → index_type N := indexing.from_nat,
    have : ∀ n, π n < π (n+1) ∨ π n = π (n+1),
    exact λ n, lt_or_eq_of_le (indexing.mono_from n.le_succ),
    rcases this (n₀ x₀ + k) with H | H ; clear this,
    { have ineq : i₀ x₀ < π (n₀ x₀ + k + 1),
      { suffices : i₀ x₀ ≤ π (n₀ x₀ + k), from lt_of_le_of_lt this H,
        rw ← indexing.from_to (i₀ x₀),
        exact indexing.mono_from ((le_max_right _ _).trans le_self_add) },
      apply hf₃,
      intros hx',
      exact lt_irrefl _ (ineq.trans_le $ hi₀ x₀ ⟨x, ⟨hx', hx⟩⟩) },
    { rw [← nat.add_one, ← add_assoc, hf₁ _ H.symm] } },
  have key' : ∀ p : ℝ × X, ∀ n ≥ n₀ p.2, f n =ᶠ[𝓝 p] λ q, f (n₀ q.2) q,
  { rintros ⟨t, x⟩ n hn,
    apply mem_of_superset (prod_mem_nhds univ_mem $ W_in x) (λ p hp, _),
    dsimp only [mem_set_of],
    calc f n p = f (n₀ x) p : key hn hp.2
    ... = f (max (n₀ x) (n₀ p.2)) p : (key (le_max_left (n₀ x) _) hp.2).symm
    ... = f (n₀ p.2) p : key (le_max_right _ _) (mem_of_mem_nhds $ W_in _) },
  have key'' : ∀ p : ℝ × X, ∀ᶠ (n : ℕ) in at_top, f n =ᶠ[𝓝 p] λ q, f (n₀ q.2) q,
  { exact λ p, (eventually_ge_at_top (n₀ p.2)).mono (λ n hn, key' p n hn) },
  refine ⟨λ t x, f (n₀ x) (t, x), _, _, _, _⟩,
  { ext x,
    rw hf0 },
  { intros t x,
    convert h₀f (n₀ x) (t, x) using 1,
    apply quotient.sound,
    exact ((key' (t, x) _ le_rfl).comp_fun (continuous.prod.mk t).continuous_at).symm },
  { intro x,
    convert (h₁f (n₀ x)).on_set x (mem_Union₂_of_mem (indexing.coe_mono $ le_max_left _ _) $ hnK x) using 1,
    apply quotient.sound,
    change (λ x', f (n₀ x') (1, x')) =ᶠ[𝓝 x] λ (x' : X), f (n₀ x) (T (n₀ x + 1), x'),
    simp_rw ← hinvf (n₀ x) 1 (T_lt _).le,
    exact ((key' (1, x) _ le_rfl).comp_fun (continuous.prod.mk 1).continuous_at).symm },
  { rintros p,
    convert h₂f (n₀ p.2) p using 1,
    apply quotient.sound,
    rw show ↿(λ t x, f (n₀ x) (t, x)) = λ p : ℝ × X, f (n₀ p.2) p, by ext ⟨s, y⟩ ; refl,
    exact (key' p _ le_rfl).symm }
end
