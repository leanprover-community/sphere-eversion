import geometry.manifold.partition_of_unity
import to_mathlib.geometry.manifold.algebra.smooth_germ
import to_mathlib.analysis.convex.basic
import to_mathlib.partition

noncomputable theory

open_locale topological_space filter manifold big_operators
open set function filter

section
variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

section
variables {F : Type*} [add_comm_group F] [module ℝ F]

lemma smooth_partition_of_unity.finite_tsupport {s : set M} (ρ : smooth_partition_of_unity ι I M s) (x : M) :
{i | x ∈ tsupport (ρ i)}.finite :=
begin
  rcases ρ.locally_finite x with ⟨t, t_in, ht⟩,
  apply ht.subset,
  rintros i hi,
  simp only [inter_comm],
  exact mem_closure_iff_nhds.mp hi t t_in
end

def smooth_partition_of_unity.index_support {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (x : M) : finset ι :=
(ρ.finite_tsupport x).to_finset

lemma smooth_partition_of_unity.mem_index_support_iff {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) (i : ι) : i ∈ ρ.index_support x ↔ x ∈ tsupport (ρ i) :=
finite.mem_to_finset _

lemma smooth_partition_of_unity.sum_germ {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (x : M) : ∑ i in ρ.index_support x, (ρ i : smooth_germ I x) = 1 :=
sorry

def smooth_partition_of_unity.combine {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) (x : M) : F := ∑ᶠ i, (ρ i x) • φ i x

include I

lemma smooth_partition_of_unity.germ_combine_mem {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) {x : M} (hx : x ∈ s . tactic.mem_univ) :
  (ρ.combine φ : germ (𝓝 x) F) ∈ really_convex_hull (smooth_germ I x) ((λ i, (φ i : germ (𝓝 x) F)) '' (ρ.index_support x)) :=
begin
  have : ((λ x', ∑ᶠ i, (ρ i x') • φ i x') : germ (𝓝 x) F) =
    ∑ i in ρ.index_support x, (ρ i : smooth_germ I x) • (φ i : germ (𝓝 x) F),
  { have : ∀ᶠ x' in 𝓝 x, ρ.combine φ x' = ∑ i in ρ.index_support x, (ρ i x') • φ i x',
    {
      sorry },
    sorry },
  erw this,
  apply sum_mem_really_convex_hull,
  { intros i hi,
    apply eventually_of_forall,
    apply ρ.nonneg },
  { apply ρ.sum_germ },
  { intros i hi,
    exact mem_image_of_mem _ hi },
end

end

section

variables {F : Type*} [add_comm_group F] [module ℝ F]

lemma exists_of_convex {P : (Σ x : M, germ (𝓝 x) F) → Prop}
  (hP : ∀ x, really_convex (smooth_germ I x) {φ | P ⟨x, φ⟩})
  (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ :=
begin
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩,
  { intros x,
    rcases hP' x with ⟨f, hf⟩,
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, λ _, id⟩ },
  choose φ U hU hφ using hP',
  rcases smooth_bump_covering.exists_is_subordinate I is_closed_univ (λ x h, hU x) with ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  refine ⟨λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x), λ x₀, _⟩,
  let g : ι → germ (𝓝 x₀) F := λ i, φ (b.c i),
  have : ((λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x)) : germ (𝓝 x₀) F) ∈
    really_convex_hull (smooth_germ I x₀) (g '' (ρ.index_support x₀)),
    from ρ.germ_combine_mem (λ i x, φ (b.c i) x) (mem_univ x₀),
  simp_rw [really_convex_iff_hull] at hP,
  apply hP x₀, clear hP,
  have H : g '' ↑(ρ.index_support x₀) ⊆ {φ : (𝓝 x₀).germ F | P ⟨x₀, φ⟩},
  { rintros _ ⟨i, hi, rfl⟩,
    exact hφ _ _ (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i $
      (ρ.mem_index_support_iff _ i).mp hi) },
  exact really_convex_hull_mono H this,
end

end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)


/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def filter.germ.value {X α : Type*} [topological_space X] {x : X} (φ : germ (𝓝 x) α) : α :=
quotient.lift_on' φ (λ f, f x) (λ f g h, by { dsimp only, rw eventually.self_of_nhds h })

variable (I)

/-- The predicate selecting germs of `cont_mdiff_at` functions.
TODO: merge with the next def that generalizes target space -/
def filter.germ.cont_mdiff_at {x : M} (φ : germ (𝓝 x) F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I 𝓘(ℝ, F) n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G] [finite_dimensional ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)


def filter.germ.mfderiv {x : M} (φ : germ (𝓝 x) N) :
  tangent_space I x →L[ℝ] tangent_space IG φ.value :=
@quotient.hrec_on _ (germ_setoid (𝓝 x) N)
  (λ φ : germ (𝓝 x) N, tangent_space I x →L[ℝ] tangent_space IG φ.value) φ (λ f, mfderiv I IG f x)
(begin
  intros f g hfg,
  sorry
end)

lemma really_convex_cont_mdiff_at (x : M) (n : ℕ∞) :
  really_convex (smooth_germ I x) {φ : germ (𝓝 x) F | φ.cont_mdiff_at I n} :=
begin
  rintros w w_pos w_supp w_sum,
  have : (support w).finite,
  sorry { apply finite_of_finsum_ne_zero,
    rw w_sum,
    exact zero_ne_one.symm },
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ F), w i • i) ⊆ fin_supp,
  sorry { rw set.finite.coe_to_finset,
    exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  sorry
end


lemma exists_cont_mdiff_of_convex'
  {P : M → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : M → F, 𝓒 n f ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M, germ (𝓝 x) F) → Prop := λ p, p.2.cont_mdiff_at I n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I x) {φ | PP ⟨x, φ⟩},
  { intros x,
    apply really_convex.inter,
    apply really_convex_cont_mdiff_at,
    dsimp only,
    let v : germ (𝓝 x) F → F := filter.germ.value,
    change really_convex (smooth_germ I x) (v ⁻¹' {y | P x y}),
    -- Here we want to argue that `v` is `ℝ`-linear and use an analogue of
    -- `convex.is_linear_preimage` for `really_convex` together with the fact
    -- that `convex` implies `really_convex` over a field.
    sorry, },
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  sorry { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    rcases mem_nhds_iff.mp U_in with ⟨V, hUV, V_op, hxV⟩,
    use f,
    apply mem_of_superset (V_op.mem_nhds hxV),
    rintros y hy,
    split,
    { exact hf.cont_mdiff_at (mem_of_superset (V_op.mem_nhds hy) hUV) },
    { exact hf' y (hUV hy) } },
  sorry/- rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ x, (hf x).1, λ x, (hf x).2⟩ -/
end

end

section

variables {E₁ E₂ F : Type*}
variables [normed_add_comm_group E₁] [normed_space ℝ E₁] [finite_dimensional ℝ E₁]
variables [normed_add_comm_group E₂] [normed_space ℝ E₂] [finite_dimensional ℝ E₂]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables {H₁ M₁ H₂ M₂ : Type*}
variables [topological_space H₁] (I₁ : model_with_corners ℝ E₁ H₁)
variables [topological_space M₁] [charted_space H₁ M₁] [smooth_manifold_with_corners I₁ M₁]
variables [sigma_compact_space M₁] [t2_space M₁]
variables [topological_space H₂] (I₂ : model_with_corners ℝ E₂ H₂)
variables [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]

local notation `𝓒` := cont_mdiff (I₁.prod I₂) 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on (I₁.prod I₂) 𝓘(ℝ, F)

/- TODO: generalize the next def? -/

def filter.germ.cont_mdiff_at_prod {x : M₁} (φ : germ (𝓝 x) $ M₂ → F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, ∀ y : M₂, cont_mdiff_at (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y)) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_set_of_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)

lemma exists_cont_mdiff_of_convex₂'
  {P : M₁ → (M₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : M₁, ∃ (U ∈ 𝓝 x) (f : M₁ → M₂ → F),
    𝓒_on n (uncurry f) (U ×ˢ (univ : set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M₁, germ (𝓝 x) (M₂ → F)) → Prop :=
    λ p, p.2.cont_mdiff_at_prod I₁ I₂ n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I₁ x) {φ | PP ⟨x, φ⟩},
  {
    sorry },
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  {
    sorry },
  letI : module ℝ (M₂ → F) := by apply_instance, -- Why is this line necessary??
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ ⟨x, y⟩, (hf x).1 y, λ x, (hf x).2⟩
end
end
