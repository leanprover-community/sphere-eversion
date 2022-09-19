import analysis.normed_space.bounded_linear_maps
import analysis.normed_space.finite_dimension

noncomputable theory

local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ


variables {𝕜 E F G Fₗ Gₗ X : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E]
  [normed_add_comm_group Fₗ] [normed_add_comm_group Gₗ] [normed_add_comm_group F]
  [normed_add_comm_group G]
  [normed_space 𝕜 E] [normed_space 𝕜 Fₗ] [normed_space 𝕜 Gₗ] [normed_space 𝕜 F] [normed_space 𝕜 G]
  [topological_space X]

lemma continuous_linear_map.le_op_norm_of_le' {𝕜 : Type*} {𝕜₂ : Type*} {E : Type*} {F : Type*}
  [normed_add_comm_group E] [seminormed_add_comm_group F] [nontrivially_normed_field 𝕜]
  [nontrivially_normed_field 𝕜₂] [normed_space 𝕜 E] [normed_space 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [ring_hom_isometric σ₁₂] (f : E →SL[σ₁₂] F) {x : E} (hx : x ≠ 0) {C : ℝ} (h : C * ∥x∥ ≤ ∥f x∥) :
  C ≤ ∥f∥ :=
begin
  apply le_of_mul_le_mul_right (h.trans (f.le_op_norm x)),
  rwa norm_pos_iff',
end

@[simp]
lemma continuous_linear_map.to_span_singleton_zero (𝕜 : Type*) {E : Type*} [seminormed_add_comm_group E] [nontrivially_normed_field 𝕜]
  [normed_space 𝕜 E] : continuous_linear_map.to_span_singleton 𝕜 (0 : E) = 0 :=
begin
  ext u,
  simp only [continuous_linear_map.to_span_singleton_apply, continuous_linear_map.zero_apply,
             linear_map.to_span_singleton_apply, linear_map.mk_continuous_apply, smul_zero]
end

@[simp]
lemma continuous_linear_map.comp_to_span_singleton_apply {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
  (φ : E →L[ℝ] ℝ) (v : E) (u : F) : (u ⬝ φ) v = (φ v) • u:=
rfl

universes u₁ u₂ u₃ u₄

/-- The natural linear map `(M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃) →ₗ[R] M × M₂ →ₗ[R] M₃` for `R`-modules `M`,
`M₂`, `M₃` over a commutative ring `R`.

If `f : M →ₗ[R] M₃` and `g : M₂ →ₗ[R] M₃` then `linear_map.coprodₗ (f, g)` is the map
`(m, n) ↦ f m + g n`. -/
def linear_map.coprodₗ (R : Type u₁) (M : Type u₂) (M₂ : Type u₃) (M₃ : Type u₄) [comm_ring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [module R M]
  [module R M₂] [module R M₃] : ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) →ₗ[R] (M × M₂ →ₗ[R] M₃) :=
{ to_fun := λ p, p.1.coprod p.2,
  map_add' := begin
    intros p q,
    apply linear_map.coe_injective,
    ext x,
    simp only [prod.fst_add, linear_map.coprod_apply, linear_map.add_apply, prod.snd_add],
    ac_refl
  end,
  map_smul' := begin
    intros r p,
    apply linear_map.coe_injective,
    ext x,
    simp only [prod.smul_fst, prod.smul_snd, linear_map.coprod_apply, linear_map.smul_apply,
               ring_hom.id_apply, smul_add]
  end }

lemma add_le_twice_max (a b : ℝ) : a + b ≤ 2*max a b :=
calc a + b ≤ max a b + max a b : add_le_add (le_max_left a b) (le_max_right a b)
... = _ : by ring

lemma is_bounded_linear_map_coprod (𝕜 : Type*) [nontrivially_normed_field 𝕜] (E : Type*) [normed_add_comm_group E]
  [normed_space 𝕜 E] (F : Type*) [normed_add_comm_group F] [normed_space 𝕜 F]
  (G : Type*) [normed_add_comm_group G] [normed_space 𝕜 G] : is_bounded_linear_map 𝕜
  (λ p : (E →L[𝕜] G) × (F →L[𝕜] G), p.1.coprod p.2) :=
{ map_add := begin
    intros,
    apply continuous_linear_map.coe_fn_injective,
    ext u,
    simp only [prod.fst_add, prod.snd_add, continuous_linear_map.coprod_apply,
               continuous_linear_map.add_apply],
    ac_refl
  end,
  map_smul := begin
    intros r p,
    apply continuous_linear_map.coe_fn_injective,
    ext x,
    simp only [prod.smul_fst, prod.smul_snd, continuous_linear_map.coprod_apply,
               continuous_linear_map.coe_smul', pi.smul_apply, smul_add],
  end,
  bound := begin
    refine ⟨2, zero_lt_two, _⟩,
    rintros ⟨φ, ψ⟩,
    apply continuous_linear_map.op_norm_le_bound,
    exact mul_nonneg zero_le_two (norm_nonneg _),
    rintros ⟨e, f⟩,
    calc ∥φ e + ψ f∥ ≤ ∥φ e∥ + ∥ψ f∥ : norm_add_le _ _
    ... ≤  ∥φ∥ * ∥e∥ + ∥ψ∥ * ∥f∥ : add_le_add (φ.le_op_norm e) (ψ.le_op_norm f)
    ... ≤ (max ∥φ∥ ∥ψ∥) * ∥e∥ + (max ∥φ∥ ∥ψ∥) * ∥f∥ : _
    ... ≤ (2*(max ∥φ∥ ∥ψ∥)) * (max ∥e∥ ∥f∥) : _,
    apply add_le_add,
    exact mul_le_mul_of_nonneg_right (le_max_left ∥φ∥ ∥ψ∥) (norm_nonneg e),
    exact mul_le_mul_of_nonneg_right (le_max_right ∥φ∥ ∥ψ∥) (norm_nonneg f),
    rw [← mul_add, mul_comm (2 : ℝ), mul_assoc],
    apply mul_le_mul_of_nonneg_left (add_le_twice_max _ _) (le_max_of_le_left $ norm_nonneg _)
  end }

/-- The natural continuous linear map `((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G)` for
normed spaces `E`, `F`, `G` over a normed field `𝕜`.

If `g₁ : E →L[𝕜] G` and `g₂ : F →L[𝕜] G` then `continuous_linear_map.coprodL (g₁, g₂)` is the map
`(e, f) ↦ g₁ e + g₂ f`. -/
def continuous_linear_map.coprodL :
  ((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G) :=
(is_bounded_linear_map_coprod 𝕜 E F G).to_continuous_linear_map

@[continuity]
lemma continuous.coprodL
  {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G}
  (hf : continuous f) (hg : continuous g) : continuous (λ x, (f x).coprod (g x)) :=
continuous_linear_map.coprodL.continuous.comp₂ hf hg

lemma continuous.prodL' {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*} [seminormed_add_comm_group E]
  [seminormed_add_comm_group Fₗ] [seminormed_add_comm_group Gₗ] [nontrivially_normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 Fₗ] [normed_space 𝕜 Gₗ] (R : Type*)
  [semiring R] [module R Fₗ] [module R Gₗ]
  [has_continuous_const_smul R Fₗ] [has_continuous_const_smul R Gₗ]
  [smul_comm_class 𝕜 R Fₗ] [smul_comm_class 𝕜 R Gₗ]
  {X : Type*} [topological_space X]
  {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ}
  (hf : continuous f) (hg : continuous g) : continuous (λ x, (f x).prod (g x)) :=
(continuous_linear_map.prodₗᵢ 𝕜).continuous.comp₂ hf hg

@[continuity]
lemma continuous.prodL {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*} [seminormed_add_comm_group E]
  [seminormed_add_comm_group Fₗ] [seminormed_add_comm_group Gₗ] [nontrivially_normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 Fₗ] [normed_space 𝕜 Gₗ]
  {X : Type*} [topological_space X]
  {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ}
  (hf : continuous f) (hg : continuous g) : continuous (λ x, (f x).prod (g x)) :=
hf.prodL' 𝕜 hg

@[continuity]
lemma continuous.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ}
  (hf : continuous f) (hg : continuous g) : continuous (λ x, (f x).comp (g x)) :=
(continuous_linear_map.apply 𝕜 (E →L[𝕜] Gₗ) : (E →L[𝕜] Fₗ) →L[𝕜]
  ((E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) →L[𝕜] E →L[𝕜] Gₗ).is_bounded_bilinear_map.continuous.comp₂ hg $
  (continuous_linear_map.compL 𝕜 E Fₗ Gₗ).continuous.comp hf

@[continuity]
lemma continuous_at.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} {x₀ : X}
  (hf : continuous_at f x₀) (hg : continuous_at g x₀) : continuous_at (λ x, (f x).comp (g x)) x₀ :=
begin
  have cont₁ := (continuous_linear_map.compL 𝕜 E Fₗ Gₗ).continuous.continuous_at.comp hf,
  have cont₂ := (continuous_linear_map.apply 𝕜 (E →L[𝕜] Gₗ) : (E →L[𝕜] Fₗ) →L[𝕜]
    ((E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) →L[𝕜] E →L[𝕜] Gₗ).is_bounded_bilinear_map.continuous,
  exact cont₂.continuous_at.comp (hg.prod cont₁)
end

section finite_dimensional

open function finite_dimensional

variables [finite_dimensional 𝕜 E]

lemma continuous_linear_map.inj_iff_antilip [complete_space 𝕜] (φ : E →L[𝕜] F) :
  injective φ ↔ ∃ K > 0, antilipschitz_with K φ :=
begin
  change injective φ.to_linear_map ↔ _,
  split,
  { rw ← linear_map.ker_eq_bot,
    exact φ.exists_antilipschitz_with },
  { rintro ⟨K, K_pos, H⟩,
    exact H.injective }
end
open_locale topological_space

lemma is_open_iff_eventually {α : Type*} [topological_space α] {s : set α} :
is_open s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
is_open_iff_mem_nhds

lemma is_closed_iff_frequently {α : Type*} [topological_space α] {s : set α} :
is_closed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s :=
begin
  rw ← closure_subset_iff_is_closed,
  apply forall_congr (λ x, _),
  rw mem_closure_iff_frequently
end

open_locale nnreal

lemma eventually_nnorm_sub_lt (x₀ : E) {ε : ℝ≥0} {ε_pos : 0 < ε} :
∀ᶠ x in 𝓝 x₀, ∥x - x₀∥₊ < ε :=
begin
  rw metric.nhds_basis_ball.eventually_iff,
  use [ε, ε_pos],
  simp [dist_eq_norm],
  exact λ x, id
end

lemma eventually_norm_sub_lt (x₀ : E) {ε : ℝ} {ε_pos : 0 < ε} :
∀ᶠ x in 𝓝 x₀, ∥x - x₀∥ < ε :=
begin
  rw metric.nhds_basis_ball.eventually_iff,
  use [ε, ε_pos],
  simp [dist_eq_norm]
end

lemma continuous_linear_map.is_open_injective [complete_space 𝕜] :
  is_open {L : E →L[𝕜] F | injective L} :=
begin
  rw is_open_iff_eventually,
  rintros φ₀ (hφ₀ : injective φ₀),
  rcases φ₀.inj_iff_antilip.mp hφ₀ with ⟨K, K_pos, H⟩,
  have : ∀ᶠ φ in 𝓝 φ₀, ∥φ - φ₀∥₊ < K⁻¹,
  { apply eventually_nnorm_sub_lt,
    apply inv_pos_of_pos K_pos },
  apply this.mono, dsimp only [set.mem_set_of_eq],
  intros φ hφ,
  apply φ.inj_iff_antilip.mpr,
  refine ⟨(K⁻¹ - ∥φ - φ₀∥₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ), _⟩,
  exact antilipschitz_with.add_sub_lipschitz_with H (φ - φ₀).lipschitz hφ
end

end finite_dimensional
