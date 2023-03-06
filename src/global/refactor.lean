
import to_mathlib.data.set.prod
import to_mathlib.data.set.lattice
import to_mathlib.data.nat.basic
import to_mathlib.topology.constructions
import to_mathlib.partition3

import global.localized_construction
import global.localisation_data
/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set filter model_with_corners metric
open_locale topological_space manifold

section

meta def prove_finiteness : tactic unit := `[intro x, apply set.to_finite]

structure local_prop (X Y : Type*) [topological_space X] :=
(s : X → set X)
(s_fin : ∀ x, (s x).finite . prove_finiteness)
(prop : Π x, (Π x' ∈ s x, germ (𝓝 x') Y) → Prop)

variables {X Y : Type*} [topological_space X]

/-- Evaluate a local property at a point on a given function. -/
def local_prop.eval  (P : local_prop X Y) (x : X) (f : X → Y) : Prop :=
P.prop x (λ x' hx', (f : germ (𝓝 x') Y))

instance : has_coe_to_fun (local_prop X Y) (λ _, X → (X → Y) → Prop) :=
⟨local_prop.eval⟩

/-- A local property depending on a single point. -/
def local_prop.single (P : Π x : X, germ (𝓝 x) Y → Prop) : local_prop X Y :=
{ s := λ x, {x},
  prop := λ x φ, P x (φ _ (mem_singleton x))  }

@[simp]
lemma local_prop.eval_single (P : Π x : X, (germ (𝓝 x) Y → Prop)) (f : X → Y) (x : X) :
  local_prop.single P x f ↔ P x f :=
iff.rfl

/-- A local property depending on a point and its image under a given function. -/
def local_prop.pair (π : X → X)
  (P : Π x : X, germ (𝓝 x) Y → germ (𝓝 $ π x) Y →  Prop) : local_prop X Y :=
{ s := λ x : X, {x, π x},
  prop := λ x φ, P x (φ x (mem_insert _ _)) (φ _ $ mem_insert_iff.mpr $ or.inr $ mem_singleton _) }

/-- The local property asserting `f x = f (π x)`. -/
def local_prop.equality (π : X → X) : local_prop X Y :=
  local_prop.pair π (λ x φ ψ, φ.value = ψ.value)

@[simp]
lemma local_prop.eval_pair {π : X → X}
  {P : Π x : X, germ (𝓝 x) Y → germ (𝓝 $ π x) Y →  Prop} {f : X → Y} {x : X} :
  local_prop.pair π P x f ↔ P x f f :=
iff.rfl

lemma local_prop.equality_iff {π : X → X} (f : X → Y) (x : X) :
  local_prop.equality π x f ↔ f x = f (π x) := iff.rfl

end


/-- Given a predicate on germs `P : (Σ x : X, germ (𝓝 x) Y) → Prop` and `A : set X`,
build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A ⟨x, f⟩) ↔ ∀ᶠ x near A, P ⟨x, f⟩`, see
`forall_restrict_germ_predicate_iff` for this equivalence. -/
def restrict_germ_predicate {X Y : Type*} [topological_space X]
  (P : (Σ x : X, germ (𝓝 x) Y) → Prop) (A : set X) : (Σ x : X, germ (𝓝 x) Y) → Prop :=
λ ⟨x, φ⟩, quotient.lift_on' φ (λ f, x ∈ A → ∀ᶠ y in 𝓝 x, P ⟨y, f⟩) begin
  have : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P ⟨y, f⟩) → ∀ᶠ y in 𝓝 x, P ⟨y, f'⟩,
  { intros f f' hff' hf,
    apply (hf.and $ eventually.eventually_nhds hff').mono,
    rintros y ⟨hy, hy'⟩,
    rwa germ.coe_eq.mpr (eventually_eq.symm hy') },
  exact λ f f' hff', propext $ forall_congr $ λ _, ⟨this f f' hff', this f' f hff'.symm⟩,
end

lemma forall_restrict_germ_predicate_iff {X Y : Type*} [topological_space X]
  {P : (Σ x : X, germ (𝓝 x) Y) → Prop} {A : set X} {f : X → Y} :
  (∀ x, restrict_germ_predicate P A ⟨x, f⟩) ↔ ∀ᶠ x near A, P ⟨x, f⟩ :=
by { rw eventually_nhds_set_iff, exact iff.rfl }

def restrict_germ_predicate' {X Y : Type*} [topological_space X]
  (P : Π x : X, germ (𝓝 x) Y → Prop) (A : set X) : Π x : X, germ (𝓝 x) Y → Prop :=
λ x φ, quotient.lift_on' φ (λ f, x ∈ A → ∀ᶠ y in 𝓝 x, P y f) begin
  have : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f',
  { intros f f' hff' hf,
    apply (hf.and $ eventually.eventually_nhds hff').mono,
    rintros y ⟨hy, hy'⟩,
    rwa germ.coe_eq.mpr (eventually_eq.symm hy') },
  exact λ f f' hff', propext $ forall_congr $ λ _, ⟨this f f' hff', this f' f hff'.symm⟩,
end

lemma forall_restrict_germ_predicate'_iff {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} :
  (∀ x, restrict_germ_predicate' P A x f) ↔ ∀ᶠ x near A, P x f :=
by { rw eventually_nhds_set_iff, exact iff.rfl }

lemma  forall_restrict_germ_predicate'_of_forall {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} (h : ∀ x, P x f) :
  ∀ x, restrict_germ_predicate' P A x f :=
forall_restrict_germ_predicate'_iff.mpr (eventually_of_forall h)

-- Replace localisation_data.Union_succ with
lemma localisation_data.Union_succ' {𝕜 : Type*} [nontrivially_normed_field 𝕜] {E : Type*} [normed_add_comm_group E]
  [normed_space 𝕜 E] {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] {E' : Type*} [normed_add_comm_group E']
  [normed_space 𝕜 E'] {H' : Type*} [topological_space H']
  {I' : model_with_corners 𝕜 E' H'} {M' : Type*} [topological_space M']
  [charted_space H' M'] [smooth_manifold_with_corners I' M'] {f : M → M'}
  (ld : localisation_data I I' f) {β : Type*} (s : ld.ι → set β) (i : index_type ld.N) :
  (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
begin
  simp only [(λ j, le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)],
  erw [bUnion_union, bUnion_singleton],
  refl
end

variables
{EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM] [finite_dimensional ℝ EM]
{HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM} [boundaryless IM]
{M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
[t2_space M] [sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX] [finite_dimensional ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[sigma_compact_space X]

{R : rel_mfld IM M IX X}
{A : set M} {δ : M → ℝ}

set_option trace.filter_inst_type true

def mk_formal_sol (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) F) : formal_sol R :=
{ bs := λ m, (F m).1.2,
  ϕ := λ m, (F m).2,
  smooth' := sorry,
  is_sol' := λ m, begin
    convert hsol m,
    refine  one_jet_bundle.ext IM M IX X _ _ _,
    rw hsec,
    all_goals { refl }
    end}

@[simp]
lemma mk_formal_sol_apply (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  :
  (mk_formal_sol F hsec hsol hsmooth : M → one_jet_bundle IM M IX X) = F :=
begin
  ext x ; try { refl },
  rw hsec,
  refl
end

@[simp]
lemma mk_formal_sol_bs_apply (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  (x : M) :
  (mk_formal_sol F hsec hsol hsmooth).bs x = (F x).1.2 :=
rfl


def mk_htpy_formal_sol (F : ℝ → M → one_jet_bundle IM M IX X) (hsec : ∀ t x, (F t x).1.1 = x)
(hsol : ∀ t x, F t x ∈ R)
(hsmooth : smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F) : htpy_formal_sol R :=
{ bs := λ t m, (F t m).1.2,
  ϕ := λ t m, (F t m).2,
  smooth' := sorry,
  is_sol' := λ t m, begin
    convert hsol t m,
    refine  one_jet_bundle.ext IM M IX X _ _ _,
    rw hsec,
    all_goals { refl }
    end}

@[simp]
lemma mk_htpy_formal_sol_apply (F : ℝ → M → one_jet_bundle IM M IX X) (hsec : ∀ t x, (F t x).1.1 = x)
(hsol : ∀ t x, F t x ∈ R)
(hsmooth : smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F) (t : ℝ) :
  (mk_htpy_formal_sol F hsec hsol hsmooth t : M → one_jet_bundle IM M IX X) = F t :=
begin
  ext x ; try { refl },
  rw hsec,
  refl
end

lemma index_type.lt_or_eq_succ (N n : ℕ) :
  (n : index_type N) < (n+1 : ℕ) ∨ (n : index_type N) = (n+1 : ℕ) :=
begin
  rw or_comm,
  exact eq_or_lt_of_le (indexing.mono_from n.le_succ)
end

lemma index_type.le_or_lt_succ {N n : ℕ} (hn : (n : index_type N) < (n+1 : ℕ)) (j : index_type N) :
  j ≤ n ↔ j < (n + 1 : ℕ) :=
begin
  cases N, { exact nat.lt_succ_iff.symm, },
  refine ⟨λ h, lt_of_le_of_lt h hn, λ h, _⟩,
  clear hn,
  obtain ⟨j, hj⟩ := j,
  change _ ≤ indexing.from_nat n,
  change _ < indexing.from_nat (n + 1) at h,
  unfold indexing.from_nat at ⊢ h,
  rcases lt_trichotomy N n with hNn | rfl | hNn,
  { replace hNn : ¬ (n < N + 1) := by simpa using nat.succ_le_iff.mpr hNn,
    simp only [hNn, not_false_iff, dif_neg],
    exact fin.le_last _ },
  { simpa using nat.lt_succ_iff.mp hj },
  { simp only [hNn, add_lt_add_iff_right, dif_pos, fin.mk_lt_mk] at h,
    simpa only [nat.lt.step hNn, dif_pos, fin.mk_le_mk] using nat.lt_succ_iff.mp h }
end

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
sorry

lemma index_type.not_lt_zero {N : ℕ} (j : index_type N) : ¬ (j < 0) :=
sorry

example {α γ : Type*} (β : α → Type*) : ((Σ a, β a) → γ) ≃ Π a, (β a → γ) :=
{ to_fun := λ f a b, f ⟨a, b⟩,
  inv_fun := λ f p, f p.1 p.2,
  left_inv := begin
    intros f,
    ext ⟨a, b⟩,
    refl
  end,
  right_inv := begin
    intros f,
    ext a,
    refl
  end }


lemma inductive_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  (init : ∃ f : X → Y, ∀ x, P₀ x f)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ x ∈ ⋃ j < i, K j, P₁ x f) →
    ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (∀ x ∈ ⋃ j ≤ i, K j, P₁ x f') ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₁ x f :=
begin
  let P : ℕ → (X → Y) → Prop :=
    λ n f, (∀ x, P₀ x f) ∧ ∀ x ∈ (⋃ i ≤ (n : index_type N) , K i), P₁ x f,
  let Q : ℕ → (X → Y) → (X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧ ∀ x ∉ U (n + 1 : ℕ), f' x = f x,
  obtain ⟨f, hf⟩ : ∃ f : ℕ → X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  { apply exists_by_induction',
    { dsimp [P],
      cases init with f₀ hf₀,
      rcases ind 0 f₀ hf₀ _ with ⟨f', h₀f', h₁f', hf'⟩,
      use [f', h₀f'],
      intros x hx,
      apply h₁f' _ hx,
      have : (⋃ (j : index_type N) (H : j < 0), K j) = ∅,
      { simp [index_type.not_lt_zero] },
      simp only [this, mem_empty_iff_false, is_empty.forall_iff, implies_true_iff] },
    { rintros n f ⟨h₀f, h₁f⟩,
      rcases index_type.lt_or_eq_succ N n with hn | hn,
      { simp_rw index_type.le_or_lt_succ hn at h₁f,
        rcases ind (n+1 : ℕ) f h₀f h₁f with ⟨f', h₀f', h₁f', hf'⟩,
        exact ⟨f', ⟨h₀f', h₁f'⟩, ⟨λ hn', (hn.ne hn'.symm).elim, hf'⟩⟩ },
      { simp only [hn] at h₁f,
        exact ⟨f, ⟨h₀f, h₁f⟩, λ hn, rfl, λ x hx, rfl⟩ } } },
  dsimp only [P, Q] at hf,
  simp only [forall_and_distrib] at hf,
  rcases hf with ⟨⟨h₀f, h₁f⟩, hf, hf'⟩,
  rcases U_fin.exists_forall_eventually_of_indexing hf' hf with ⟨F, hF⟩,
  refine ⟨F, λ x, _⟩,
  have : ∀ᶠ (n : ℕ) in at_top, x ∈ ⋃ i ≤ (n : index_type N), K i,
  { have : x ∈ ⋃ (i : index_type N), K i := K_cover.symm ▸ (mem_univ x),
    rcases mem_Union.mp this with ⟨i, hi⟩,
    apply (filter.tendsto_at_top.mp (index_type.tendsto_coe_at_top N) i).mono,
    intros n hn,
    exact mem_Union₂.mpr ⟨i, hn, hi⟩ },
  rcases eventually_at_top.mp ((hF x).and this) with ⟨n₀, hn₀⟩,
  rcases hn₀ n₀ le_rfl with ⟨hx, hx'⟩,
  rw germ.coe_eq.mpr hx.symm,
  exact ⟨h₀f n₀ x, h₁f n₀ x hx'⟩
end

lemma forall₂_and_distrib {α β : Sort*} {p q : α → β → Prop} :
  (∀ x y, p x y ∧ q x y) ↔ (∀ x y, p x y) ∧ ∀ x y, q x y :=
begin
  split ; intros h,
  split ; intros,
  exact (h x y).1,
  exact (h x y).2,
  intros x y,
   exact ⟨h.1 x y, h.2 x y⟩
end

.
open_locale filter

lemma filter.eventually_eq.comp_fun {α β γ : Type*} {f g : β → γ} {l : filter α} {l' : filter β}
  (h : f =ᶠ[l'] g) {φ : α → β} (hφ : tendsto φ l l') : f ∘ φ =ᶠ[l] g ∘ φ :=
hφ h

def filter.germ.slice_left {X Y Z : Type*} [topological_space X] [topological_space Y] {x : X} {y : Y}
  (P : germ (𝓝 (x, y)) Z) : germ (𝓝 x) Z :=
P.lift_on (λ f, ((λ x', f (x', y)) : germ (𝓝 x) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 x).germ_setoid Z) _ _
     (hfg.comp_fun (continuous.prod.mk_left y).continuous_at))

-- The following version is needed because prod.mk.eta isn't refl.
def filter.germ.slice_left' {X Y Z : Type*} [topological_space X] [topological_space Y] {p : X × Y}
  (P : germ (𝓝 p) Z) : germ (𝓝 p.1) Z :=
P.lift_on (λ f, ((λ x', f (x', p.2)) : germ (𝓝 p.1) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 p.1).germ_setoid Z) _ _
     (hfg.comp_fun begin
       rw ← (prod.mk.eta : (p.1, p.2) = p),
       exact (continuous.prod.mk_left p.2).continuous_at,
     end))

def filter.germ.slice_right {X Y Z : Type*} [topological_space X] [topological_space Y] {x : X} {y : Y}
  (P : germ (𝓝 (x, y)) Z) : germ (𝓝 y) Z :=
P.lift_on (λ f, ((λ y', f (x, y')) : germ (𝓝 y) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 y).germ_setoid Z) _ _
     (hfg.comp_fun (continuous.prod.mk x).continuous_at))

-- The following version is needed because prod.mk.eta isn't refl.
def filter.germ.slice_right' {X Y Z : Type*} [topological_space X] [topological_space Y] {p : X × Y}
  (P : germ (𝓝 p) Z) : germ (𝓝 p.2) Z :=
P.lift_on (λ f, ((λ y, f (p.1, y)) : germ (𝓝 p.2) Z))
  (λ f g hfg, @quotient.sound _ ((𝓝 p.2).germ_setoid Z) _ _
     (hfg.comp_fun begin
       rw ← (prod.mk.eta : (p.1, p.2) = p),
       exact (continuous.prod.mk p.1).continuous_at,
     end))

private def T : ℕ → ℝ := λ n, nat.rec 0 (λ k x, x + 1/(2 : ℝ)^(k+1)) n

private lemma T_lt (n : ℕ) : T n < 1 := sorry

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

lemma T_one : T 1 = 1/2 :=
by simp [T]

private lemma not_T_succ_le (n : ℕ) : ¬ T (n + 1) ≤ 0 := sorry


lemma filter.eventually_eq.eventually_eq_ite {X Y : Type*} {l : filter X} {f g : X → Y}
  {P : X → Prop} [decidable_pred P] (h : f =ᶠ[l] g) :
(λ x, if P x then f x else g x) =ᶠ[l] f :=
begin
  apply h.mono (λ x hx, _),
  dsimp only,
  split_ifs ; tauto
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
    ((∀ p : ℝ × X, P₀ p.2 (filter.germ.slice_right' (f n)) ∧ P₂ p (f n)) ∧
    (∀ᶠ x near (⋃ i ≤ (n : index_type N) , K i), P₁ x (filter.germ.slice_right' (f n : (𝓝 (T (n+1), x)).germ Y))) ∧
    (∀ t ≥ T (n+1), ∀ x, f n (t, x) = f n (T (n+1), x)) ∧ (∀ x, f n (0, x) = f₀ x) ∧
    (∀ᶠ t in 𝓝 (T $ n+1), ∀ x, f n (t, x) = f n (T (n+1), x))) ∧
    (((((n+1:ℕ) : index_type N) = n) → f (n+1) = f n) ∧
      ∀ x ∉ U (n + 1 : ℕ), ∀ t, f (n+1) (t, x) = f n (t, x))
   :=
begin
  let P₀' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₀ p.2 φ.slice_right' ∧ P₂ p φ,
  let P₁' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₁ p.2 φ.slice_right',
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
  let P₀' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₀ p.2 φ.slice_right' ∧ P₂ p φ,
  let P₁' : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₁ p.2 φ.slice_right',
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

-- temporary assumptions to avoid stupid case disjunction and instance juggling

variables [nonempty M] [nonempty X] [locally_compact_space M] [locally_compact_space X]

local notation `J¹` := one_jet_bundle IM M IX X

def is_holonomic_germ {x : M} (φ : germ (𝓝 x) J¹) : Prop :=
quotient.lift_on' φ (λ F, mfderiv IM IX (λ x', (F x').1.2) x  = (F x).2)
begin
  letI : setoid (M → J¹) := (𝓝 x).germ_setoid (one_jet_bundle IM M IX X),
  have key : ∀ f g, f ≈ g → (λ (F : M → one_jet_bundle IM M IX X), mfderiv IM IX (λ (x' : M), (F x').fst.snd) x = (F x).snd) f →
  (λ (F : M → one_jet_bundle IM M IX X), mfderiv IM IX (λ (x' : M), (F x').fst.snd) x = (F x).snd) g,
  { intros f g hfg hf,
    have hfg' : (λ x', (f x').1.2) =ᶠ[𝓝 x] (λ x', (g x').1.2),
      from hfg.fun_comp (λ s, s.1.2),
    rw [← hfg'.mfderiv_eq, hf, hfg.self_of_nhds] },
  exact λ f g H, propext ⟨key f g H, key g f H.symm⟩,
end

lemma is_holonomic_germ_mk_formal_sol (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  (x : M) :
  is_holonomic_germ (F : germ (𝓝 x) J¹) ↔ (mk_formal_sol F hsec hsol hsmooth).is_holonomic_at x :=
iff.rfl

lemma rel_mfld.ample.satisfies_h_principle (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  R.satisfies_h_principle A δ :=
begin
  borelize EX,
  refine rel_mfld.satisfies_h_principle_of_weak hA _,
  unfreezingI { clear_dependent A },
  intros A hA 𝓕₀ h𝓕₀,

  have cont : continuous 𝓕₀.bs, from 𝓕₀.smooth_bs.continuous,
  let L : localisation_data IM IX 𝓕₀.bs := std_localisation_data EM IM EX IX cont,
  let K : index_type L.N → set M := λ i, (L.φ i) '' (closed_ball (0:EM) 1),
  let U : index_type L.N → set M := λ i, range (L.φ i),
  have K_cover : (⋃ i, K i) = univ,
    from eq_univ_of_subset (Union_mono (λ i, image_subset _ ball_subset_closed_ball)) L.h₁,
  let τ := λ x : M, min (δ x) (L.ε x),
  have τ_pos : ∀ x, 0 < τ x, from λ x, lt_min (hδ_pos x) (L.ε_pos x),
  have τ_cont : continuous τ, from hδ_cont.min L.ε_cont,
  have := (λ (x : M) (F' : germ (𝓝 x) J¹), F'.value = 𝓕₀ x),
  let P₀ : Π x : M, germ (𝓝 x) J¹ → Prop := λ x F,
    F.value.1.1 = x ∧
    F.value ∈ R ∧
    F.cont_mdiff_at' IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
    restrict_germ_predicate' (λ x F', F'.value = 𝓕₀ x) A x F ∧
    dist (F.value.1.2) (𝓕₀.bs x) < τ x,

  let P₁ : Π x : M, germ (𝓝 x) J¹ → Prop := λ x F, is_holonomic_germ F,
  let P₂ : Π p : ℝ × M, germ (𝓝 p) J¹ → Prop := λ p F,
    F.cont_mdiff_at' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞,
  have hP₂ : ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → one_jet_bundle IM M IX X),
    P₂ (a*p.1+b, p.2) f → P₂ p (λ p : ℝ × M, f (a*p.1+b, p.2)),
  { rintros a b ⟨t, x⟩ f h,
    change cont_mdiff_at _ _ _ (f ∘ λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    change cont_mdiff_at _ _ _ f ((λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x)) at h,
    have : cont_mdiff_at (𝓘(ℝ, ℝ).prod IM) (𝓘(ℝ, ℝ).prod IM) ∞ (λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    { have h₁ : cont_mdiff_at 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (λ t, a * t + b) t,
      from cont_mdiff_at_iff_cont_diff_at.mpr
        (((cont_diff_at_id : cont_diff_at ℝ ∞ id t).const_smul a).add cont_diff_at_const),
      exact h₁.prod_map cont_mdiff_at_id },
    exact h.comp (t, x) this },
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹),
  { refine λ x, ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩,
    { revert x,
      exact forall_restrict_germ_predicate'_of_forall (λ x, rfl) },
    { erw dist_self,
      exact τ_pos x } },
  have ind : ∀ (i : index_type L.N) (f : M → J¹), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → M → J¹, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1),
  { intros i f hf₀ hf₁,
    let K₀ : set EM := closed_ball 0 1,
    have hK₀ : is_compact K₀, from is_compact_closed_ball 0 1,
    let K₁ : set EM := closed_ball 0 2,
    have hK₁ : is_compact K₁, from is_compact_closed_ball 0 2,
    have hK₀K₁ : K₀ ⊆ interior K₁,
    { dsimp [K₀, K₁],
      rw interior_closed_ball (0 : EM) (by norm_num : (2 : ℝ) ≠ 0),
      exact closed_ball_subset_ball (by norm_num) },
    let C := ⋃ j < i, (L.φ j) '' closed_ball 0 1,
    have hC : is_closed C,
    { -- TODO: rewrite localization_data.is_closed_Union to match this.
      exact is_closed_bUnion (finite_Iio _) (λ j hj, (hK₀.image $ (L.φ j).continuous).is_closed) },
    simp only [P₀, forall_and_distrib] at hf₀,
    rcases hf₀ with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩,
    rw forall_restrict_germ_predicate'_iff at hf_A,
    let F : formal_sol R := mk_formal_sol f hf_sec hf_sol hf_smooth,
    have hFAC : ∀ᶠ x near A ∪ C, F.is_holonomic_at x,
    { rw eventually_nhds_set_union,
      refine ⟨_, hf₁⟩,
      apply (hf_A.and h𝓕₀).eventually_nhds_set.mono (λ x hx, _),
      rw eventually_and at hx,
      apply hx.2.self_of_nhds.congr,
      apply hx.1.mono (λ x' hx', _),
      simp [F],
      exact hx'.symm },
    have hFφψ : F.bs '' (range $ L.φ i) ⊆ range (L.ψj i),
    { rw ← range_comp,
      apply L.ε_spec,
      intro x,
      calc dist (F.bs x) (𝓕₀.bs x) = dist (f x).1.2 (𝓕₀.bs x) : by simp only [F, mk_formal_sol_bs_apply]
      ... < τ x : hf_dist x
      ... ≤ L.ε x : min_le_right _ _ },
    let η : M → ℝ := λ x, τ x - dist (f x).1.2 (𝓕₀.bs x),
    have η_pos : ∀ x, 0 < η x,
    { exact λ x, sub_pos.mpr (hf_dist x) },
    have η_cont : continuous η,
    { have : cont_mdiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f, from λ x, hf_smooth x,
      apply τ_cont.sub,
      exact ((one_jet_bundle_proj_continuous IM M IX X).comp this.continuous).snd.dist
        𝓕₀.smooth_bs.continuous },
    rcases (L.φ i).improve_formal_sol (L.ψj i) hRample hRopen (hA.union hC) η_pos η_cont hFφψ hFAC
      hK₀ hK₁ hK₀K₁ with ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩,
    refine ⟨λ t x, F' t x, _, _, _, _, _, _⟩,
    { refine λ t x, ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩,
      { revert x,
        rw forall_restrict_germ_predicate'_iff,
        rw [eventually_nhds_set_union] at hF'AC,
        apply (hF'AC.1.and hf_A).mono,
        rintros x ⟨hx, hx'⟩,
        change F' t x = _,
        rw [hx t, ← hx', mk_formal_sol_apply],
        refl },
      { calc dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) : dist_triangle _ _ _
        ... < η x + dist (F.bs x) (𝓕₀.bs x) : add_lt_add_right (hF'η t x) _
        ... = τ x : by simp [η] } },
    { rw [union_assoc, eventually_nhds_set_union] at hF'hol,
      replace hF'hol := hF'hol.2,
      simp_rw [← L.Union_succ'] at hF'hol,
      exact hF'hol },
    { exact F'.smooth },
    { intros t x hx,
      rw hF'K₁ t x ((mem_range_of_mem_image _ _).mt hx),
      simp [F] },
    { apply hF'₀.mono (λ x hx, _),
      erw hx,
      ext1 y,
      simp [F] },
    { apply hF'₁.mono (λ x hx, _),
      rw hx } },
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ L.lf_φ K_cover init ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩,
  simp only [P₀, forall₂_and_distrib] at hFP₀,
  rcases hFP₀ with ⟨hF_sec, hF_sol, hF_smooth, hF_A, hF_dist⟩,
  refine ⟨mk_htpy_formal_sol F hF_sec hF_sol hFP₂, _, _, _, _⟩,
  { intros x,
    rw [mk_htpy_formal_sol_apply, hF₀] },
  { exact hFP₁ },
  { intros x hx t,
    rw mk_htpy_formal_sol_apply,
    exact (forall_restrict_germ_predicate'_iff.mp $ hF_A t).on_set x hx },
  { intros t x,
    change dist (mk_htpy_formal_sol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x,
    rw mk_htpy_formal_sol_apply,
    exact (hF_dist t x).le.trans (min_le_left _ _) }
end
