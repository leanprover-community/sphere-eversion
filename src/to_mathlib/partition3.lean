import geometry.manifold.partition_of_unity
import tactic.find_unused
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

def smooth_partition_of_unity.fintsupport {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (x : M) : finset ι :=
(ρ.finite_tsupport x).to_finset

lemma smooth_partition_of_unity.mem_fintsupport_iff {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) (i : ι) : i ∈ ρ.fintsupport x ↔ x ∈ tsupport (ρ i) :=
finite.mem_to_finset _

lemma locally_finite.eventually_subset {ι X : Type*} [topological_space X] {s : ι → set X}
(hs : locally_finite s) (hs' : ∀ i, is_closed (s i)) (x : X) :
∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} :=
begin
  apply mem_of_superset (hs.Inter_compl_mem_nhds hs' x),
  intros y hy i hi,
  simp only [mem_Inter, mem_compl_iff] at hy,
  exact not_imp_not.mp (hy i) hi
end

lemma smooth_partition_of_unity.eventually_fintsupport_subset {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x :=
(ρ.locally_finite.closure.eventually_subset (λ _, is_closed_closure) x).mono
  (λ y, finite.to_finset_subset.mpr)

def smooth_partition_of_unity.finsupport {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
[finite_dimensional ℝ E] {H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M]
[smooth_manifold_with_corners I M] {s} (ρ : smooth_partition_of_unity ι I M s) (x : M) : finset ι :=
ρ.to_partition_of_unity.finsupport x

/-- Weaker version of `smooth_partition_of_unity.eventually_fintsupport_subset`. -/
lemma smooth_partition_of_unity.finsupport_subset_fintsupport {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ρ.finsupport x ⊆ ρ.fintsupport x :=
begin
  rintros i hi,
  rw ρ.mem_fintsupport_iff,
  apply subset_closure,
  exact (ρ.to_partition_of_unity.mem_finsupport x).mp hi,
end

lemma smooth_partition_of_unity.eventually_finsupport_subset {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x :=
begin
  apply (ρ.eventually_fintsupport_subset x).mono,
  exact λ y hy, (ρ.finsupport_subset_fintsupport y).trans hy
end

/-- Try to prove something is in the interior of a set by using this set is `univ`. -/
meta def tactic.mem_interior_univ : tactic unit := `[rw interior_univ; apply set.mem_univ]

lemma smooth_partition_of_unity.sum_germ {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  {x : M} (hx : x ∈ interior s . tactic.mem_interior_univ) :
∑ i in ρ.fintsupport x, (ρ i : smooth_germ I x) = 1 :=
begin
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s,
  { exact is_open_interior.eventually_mem hx },
  have : ∀ᶠ y in 𝓝 x, (⇑∑ (i : ι) in ρ.fintsupport x, ρ i) y = 1,
  { apply ((ρ.eventually_finsupport_subset x).and this).mono,
    rintros y ⟨hy, hy'⟩,
    rw [smooth_map.coe_sum, finset.sum_apply],
    apply ρ.to_partition_of_unity.sum_finsupport' (interior_subset hy') hy },
  rw [← smooth_germ.coe_sum],
  exact smooth_germ.coe_eq_coe _ _ 1 this,
end

def smooth_partition_of_unity.combine {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) (x : M) : F := ∑ᶠ i, ρ i x • φ i x

include I

lemma smooth_partition_of_unity.germ_combine_mem {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) {x : M} (hx : x ∈ interior s . tactic.mem_interior_univ) :
  (ρ.combine φ : germ (𝓝 x) F) ∈ really_convex_hull (smooth_germ I x) ((λ i, (φ i : germ (𝓝 x) F)) '' (ρ.fintsupport x)) :=
begin
  change x ∈ interior s at hx,
  have : ((λ x', ∑ᶠ i, (ρ i x') • φ i x') : germ (𝓝 x) F) =
    ∑ i in ρ.fintsupport x, (ρ i : smooth_germ I x) • (φ i : germ (𝓝 x) F),
  { have : ∀ᶠ x' in 𝓝 x, ρ.combine φ x' = ∑ i in ρ.finsupport x, (ρ i x') • φ i x',
    {
      sorry },
    sorry },
  erw this,
  apply sum_mem_really_convex_hull,
  { intros i hi,
    apply eventually_of_forall,
    apply ρ.nonneg },
  { apply ρ.sum_germ hx },
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
    really_convex_hull (smooth_germ I x₀) (g '' (ρ.fintsupport x₀)),
    from ρ.germ_combine_mem (λ i x, φ (b.c i) x),
  simp_rw [really_convex_iff_hull] at hP,
  apply hP x₀, clear hP,
  have H : g '' ↑(ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).germ F | P ⟨x₀, φ⟩},
  { rintros _ ⟨i, hi, rfl⟩,
    exact hφ _ _ (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i $
      (ρ.mem_fintsupport_iff _ i).mp hi) },
  exact really_convex_hull_mono H this,
end

end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)


namespace filter.germ
/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [topological_space X] {x : X} (φ : germ (𝓝 x) α) : α :=
quotient.lift_on' φ (λ f, f x) (λ f g h, by { dsimp only, rw eventually.self_of_nhds h })

lemma value_smul {X α β : Type*} [topological_space X] {x : X} [has_smul α β]
  (φ : germ (𝓝 x) α) (ψ : germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl))

@[to_additive]
def value_mul_hom {X E : Type*} [monoid E] [topological_space X] {x : X} :
  germ (𝓝 x) E →* E :=
{ to_fun := filter.germ.value,
  map_one' := rfl,
  map_mul' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl)) }

def valueₗ {X 𝕜 E : Type*} [semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space X] {x : X} : germ (𝓝 x) E →ₗ[𝕜] E :=
{ map_smul' := λ r φ, germ.induction_on φ (λ f, rfl),
  .. filter.germ.value_add_hom }

def value_ring_hom {X E : Type*} [semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+* E :=
{ ..filter.germ.value_mul_hom,
  ..filter.germ.value_add_hom }

def value_order_ring_hom {X E : Type*} [ordered_semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+*o E :=
{ monotone' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g h, h.self_of_nhds)),
  ..filter.germ.value_ring_hom }

def _root_.subring.ordered_subtype {R} [ordered_ring R] (s : subring R) : s →+*o R :=
{ monotone' := λ x y h, h,
  ..s.subtype }

def _root_.smooth_germ.value_order_ring_hom (x : N) : smooth_germ IG x →+*o ℝ :=
filter.germ.value_order_ring_hom.comp $ subring.ordered_subtype _

def _root_.smooth_germ.value_ring_hom (x : N) : smooth_germ IG x →+* ℝ :=
filter.germ.value_ring_hom.comp $ subring.subtype _

lemma _root_.smooth_germ.value_order_ring_hom_to_ring_hom (x : N) :
  (smooth_germ.value_order_ring_hom IG x).to_ring_hom  = smooth_germ.value_ring_hom IG x :=
rfl

def valueₛₗ (x : N) : germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom IG x] F :=
{ to_fun := filter.germ.value,
  map_smul' := λ φ ψ, value_smul (φ : germ (𝓝 x) ℝ) ψ,
  .. filter.germ.value_add_hom }
end filter.germ

variable (I)

/-- The predicate selecting germs of `cont_mdiff_at` functions.
TODO: merge with the next def that generalizes target space -/
def filter.germ.cont_mdiff_at {x : M} (φ : germ (𝓝 x) F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I 𝓘(ℝ, F) n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

lemma smooth_germ.germ.cont_mdiff_at {x : M} {φ : smooth_germ I x} {n : ℕ∞} :
  (φ : germ (𝓝 x) ℝ).cont_mdiff_at I n :=
sorry -- unused

lemma filter.germ.cont_mdiff_at_add {x : M} {φ ψ : germ (𝓝 x) F} {n : ℕ∞}
(hφ : φ.cont_mdiff_at I n) (hψ : ψ.cont_mdiff_at I n) :
  (φ + ψ).cont_mdiff_at I n :=
begin
  refine germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg, _)) hφ hψ,
  exact hf.add hg
end

lemma filter.germ.cont_mdiff_at.smul {x : M} {φ : germ (𝓝 x) F} {n : ℕ∞}
(hφ : φ.cont_mdiff_at I n) (a : smooth_germ I x) :
  (a • φ).cont_mdiff_at I n :=
begin
  rcases a with ⟨ψ, g, rfl⟩,
  refine germ.induction_on φ (λ f hf, _) hφ,
  sorry
  -- exact cont_mdiff_at.smul g.2 hf
end


lemma filter.germ.cont_mdiff_at_sum {x : M} {s : finset (germ (𝓝 x) F)} {n : ℕ∞}
(h : ∀ φ : germ (𝓝 x) F, φ ∈ s → φ.cont_mdiff_at I n) (w : (𝓝 x).germ F → ↥(smooth_germ I x)) :
  (∑ φ in s, w φ • φ).cont_mdiff_at I n :=
begin
  classical,
  induction s using finset.induction_on with φ s hφs hs,
  { rw [finset.sum_empty],
    exact cont_mdiff_at_const },
  simp only [finset.mem_insert, forall_eq_or_imp] at h,
  specialize hs h.2, replace h := h.1,
  rw finset.sum_insert hφs,
  exact filter.germ.cont_mdiff_at_add _ (h.smul _ _) hs
end

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
(λ f g hfg, heq_of_eq (eventually_eq.mfderiv_eq hfg : _))

lemma really_convex_cont_mdiff_at (x : M) (n : ℕ∞) :
  really_convex (smooth_germ I x) {φ : germ (𝓝 x) F | φ.cont_mdiff_at I n} :=
begin
  classical,
  rw [nontrivial.really_convex_iff],
  rintros w w_pos w_supp w_sum,
  have : (support w).finite,
  { apply finite_of_finsum_ne_zero,
    rw w_sum,
    exact zero_ne_one.symm },
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ F), w i • i) ⊆ fin_supp,
  { rw set.finite.coe_to_finset,
    exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  apply filter.germ.cont_mdiff_at_sum,
  intros φ hφ,
  apply w_supp,
  simpa [fin_supp] using hφ
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
    let v : germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom I x] F := filter.germ.valueₛₗ I x,
    change really_convex (smooth_germ I x) (v ⁻¹' {y | P x y}),
    dsimp only [← smooth_germ.value_order_ring_hom_to_ring_hom] at v,
    apply really_convex.preimageₛₗ,
    rw [really_convex_iff_convex],
    apply hP },
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    rcases mem_nhds_iff.mp U_in with ⟨V, hUV, V_op, hxV⟩,
    use f,
    apply mem_of_superset (V_op.mem_nhds hxV),
    rintros y hy,
    split,
    { exact hf.cont_mdiff_at (mem_of_superset (V_op.mem_nhds hy) hUV) },
    { exact hf' y (hUV hy) } },
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ x, (hf x).1, λ x, (hf x).2⟩
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

@[main_declaration]
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
#list_unused_decls []
