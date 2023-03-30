import topology.path_connected
import topology.urysohns_lemma
import topology.uniform_space.separation
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
import topology.algebra.order.floor
import topology.shrinking_lemma
import topology.metric_space.emetric_paracompact
import analysis.convex.normed

noncomputable theory

open set function filter topological_space
open_locale unit_interval topology uniformity filter classical

section to_specific_limits

lemma tendsto_self_div_add_at_top_nhds_1_nat :
  tendsto (λ n : ℕ, (n : ℝ) / (n + 1)) at_top (𝓝 1) :=
begin
  suffices : tendsto (λ n : ℕ, (1 : ℝ) - 1 / (n + 1)) at_top (𝓝 (1 - 0)),
  { have hn : ∀ n : ℕ, (n : ℝ) + 1 ≠ 0 := λ n, n.cast_add_one_pos.ne',
    simp_rw [one_sub_div (hn _), add_sub_cancel, sub_zero] at this, exact this },
  exact tendsto_const_nhds.sub tendsto_one_div_add_at_top_nhds_0_nat
end


end to_specific_limits

section maps
open function set
variables {α β : Type*} [topological_space α] [topological_space β] {f : α → β} {g : β → α}

lemma function.left_inverse.mem_preimage_iff (hfg : left_inverse g f) {s : set α} {x : α} :
  f x ∈ g ⁻¹' s ↔ x ∈ s :=
by rw [set.mem_preimage, hfg x]

-- to set.basic
lemma function.left_inverse.image_eq (hfg : left_inverse g f) (s : set α) :
  f '' s = range f ∩ g ⁻¹' s :=
-- begin
--   simp_rw [set.ext_iff, mem_image, mem_inter_iff, mem_range, and_comm (_ ∈ _),
--     @eq_comm _ (f _), ← exists_and_distrib_right, ← exists_prop],
--   simp only [hfg _, iff_true_intro iff.rfl, implies_true_iff, hfg.mem_preimage_iff] {contextual := tt},
-- end
begin
  ext x, split,
  { rintro ⟨x, hx, rfl⟩, exact ⟨mem_range_self x, hfg.mem_preimage_iff.mpr hx⟩ },
  { rintro ⟨⟨x, rfl⟩, b⟩, exact mem_image_of_mem f (hfg.mem_preimage_iff.mp b) }
end

lemma function.left_inverse.is_open_map {f : α → β} {g : β → α} (hfg : left_inverse g f)
  (hf : is_open (range f)) (hg : continuous_on g (range f)) : is_open_map f :=
by { intros U hU, rw [hfg.image_eq], exact hg.preimage_open_of_open hf hU }

end maps

section -- to separation

lemma filter.eventually.closed_neighborhood {α} [topological_space α] [normal_space α] {C : set α}
  {P : α → Prop} (hP : ∀ᶠ x in 𝓝ˢ C, P x) (hC : is_closed C) :
    ∃ C' ∈ 𝓝ˢ C, is_closed C' ∧ ∀ᶠ x in 𝓝ˢ C', P x :=
begin
  obtain ⟨O, hO, hCO, hPO⟩ := mem_nhds_set_iff_exists.mp hP,
  obtain ⟨U, hU, hCU, hUO⟩ := normal_exists_closure_subset hC hO hCO,
  exact ⟨closure U, mem_of_superset (hU.mem_nhds_set.mpr hCU) subset_closure, is_closed_closure,
    eventually_of_mem (hO.mem_nhds_set.mpr hUO) hPO⟩
end

end

section

variables {α β : Type*} [topological_space α] [topological_space β]


lemma continuous_at.eventually {f : α → β} {a₀ : α} (hf : continuous_at f a₀)
  (P : β → Prop) (hP : is_open {b | P b}) (ha₀ : P (f a₀)) :
  ∀ᶠ a in 𝓝 a₀, P (f a) :=
hf (is_open_iff_mem_nhds.mp hP _ ha₀)

lemma continuous_at.eventually' {f : α → β} {a₀ : α} (hf : continuous_at f a₀)
  (P : β → Prop)(hP : ∀ᶠ y in 𝓝 (f a₀), P y) :
  ∀ᶠ a in 𝓝 a₀, P (f a) :=
begin
  rw [continuous_at, tendsto_iff_comap] at hf,
  exact eventually.filter_mono hf (hP.comap f)
end

lemma continuous.eventually {f : α → β} {a₀ : α} (hf : continuous f) (P : β → Prop)
  (hP : is_open {b | P b}) (ha₀ : P (f a₀)) :
  ∀ᶠ a in 𝓝 a₀, P (f a) :=
hf.continuous_at.eventually P hP ha₀

-- (unused)
lemma nhds_set_prod_le {s : set α} {t : set β} : 𝓝ˢ (s ×ˢ t) ≤ (𝓝ˢ s).prod (𝓝ˢ t) :=
begin
  intros w hw,
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp hw,
  rw [← subset_interior_iff_mem_nhds_set] at hu hv ⊢,
  refine (prod_mono hu hv).trans _,
  rw [← interior_prod_eq],
  exact interior_mono huv
end

instance [sigma_compact_space α] [sigma_compact_space β] : sigma_compact_space (α × β) :=
begin
  refine ⟨⟨λ n, compact_covering α n.unpair.1 ×ˢ compact_covering β n.unpair.2, λ n,
    (is_compact_compact_covering _ _).prod (is_compact_compact_covering _ _), _⟩⟩,
  simp_rw [set.Union_unpair (λ n m, compact_covering α n ×ˢ compact_covering β m), ← prod_Union,
    ← Union_prod_const, Union_compact_covering, univ_prod_univ]
end

end

section

lemma support_norm {α E : Type*} [normed_add_comm_group E] (f : α → E) : support (λ a, ‖f a‖) = support f :=
function.support_comp_eq norm (λ x, norm_eq_zero) f

@[to_additive]
lemma has_compact_mul_support_of_subset {α β : Type*} [topological_space α] [t2_space α]
  [has_one β] {f : α → β} {K : set α} (hK : is_compact K) (hf : mul_support f ⊆ K) :
  has_compact_mul_support f :=
is_compact_of_is_closed_subset hK (is_closed_mul_tsupport f) (closure_minimal hf hK.is_closed)

lemma periodic_const {α β : Type*} [has_add α] {a : α} {b : β} : periodic (λ x, b) a :=
λ x, rfl

lemma real.ball_zero_eq (r : ℝ) : metric.ball (0 : ℝ) r = Ioo (-r) r :=
by { ext x, simp [real.norm_eq_abs, abs_lt] }

end

section
/-! ## The standard ℤ action on ℝ is properly discontinuous

TODO: use that in to_mathlib.topology.periodic?
-/
instance : has_vadd ℤ ℝ := ⟨λ n x, (n : ℝ) + x⟩

instance : properly_discontinuous_vadd ℤ ℝ :=
⟨begin
  intros K L hK hL,
  rcases eq_empty_or_nonempty K with rfl | hK' ; rcases eq_empty_or_nonempty L with rfl | hL' ;
  try { simp },
  have hSK:= (hK.is_lub_Sup hK').1,
  have hIK:= (hK.is_glb_Inf hK').1,
  have hSL:= (hL.is_lub_Sup hL').1,
  have hIL:= (hL.is_glb_Inf hL').1,
  apply (finite_Icc ⌈Inf L - Sup K⌉ ⌊Sup L - Inf K⌋).subset,
  rintros n (hn : has_vadd.vadd n '' K ∩ L ≠ ∅),
  rcases nonempty_iff_ne_empty.mpr hn with ⟨l, ⟨k, hk, rfl⟩, hnk : (n : ℝ) + k ∈ L⟩,
  split,
  { rw int.ceil_le,
    linarith [hIL hnk, hSK hk] },
  { rw int.le_floor,
    linarith [hSL hnk, hIK hk] }
end⟩

end

section fract

open int
/- properties of the (dis)continuity of `int.fract` on `ℝ`.
To be PRed to topology.algebra.floor_ring
-/

lemma floor_eq_self_iff {x : ℝ} : (⌊x⌋ : ℝ) = x ↔ ∃ n : ℤ, x = n :=
begin
  split,
  { intro h,
    exact ⟨⌊x⌋, h.symm⟩ },
  { rintros ⟨n, rfl⟩,
    rw floor_int_cast }
end

lemma fract_eq_zero_iff {x : ℝ} : fract x = 0 ↔ ∃ n : ℤ, x = n :=
by rw [fract, sub_eq_zero, eq_comm, floor_eq_self_iff]

lemma fract_ne_zero_iff {x : ℝ} : fract x ≠ 0 ↔ ∀ n : ℤ, x ≠ n :=
by rw [← not_exists, not_iff_not, fract_eq_zero_iff]

lemma Ioo_floor_mem_nhds {x : ℝ} (h : ∀ (n : ℤ), x ≠ n) : Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1 : ℝ) ∈ 𝓝 x :=
Ioo_mem_nhds ((floor_le x).eq_or_lt.elim (λ H, (h ⌊x⌋ H.symm).elim) id) (lt_floor_add_one x)

lemma loc_constant_floor {x : ℝ} (h : ∀ (n : ℤ), x ≠ n) : floor =ᶠ[𝓝 x] (λ x', ⌊x⌋) :=
begin
  filter_upwards [Ioo_floor_mem_nhds h],
  intros y hy,
  rw floor_eq_on_Ico,
  exact mem_Ico_of_Ioo hy
end

lemma fract_eventually_eq {x : ℝ}
  (h : fract x ≠ 0) : fract =ᶠ[𝓝 x] (λ x', x' - floor x) :=
begin
  rw fract_ne_zero_iff at h,
  exact eventually_eq.rfl.sub ((loc_constant_floor h).fun_comp _)
end

-- todo: make iff
lemma continuous_at_fract {x : ℝ} (h : fract x ≠ 0) : continuous_at fract x :=
(continuous_at_id.sub continuous_at_const).congr (fract_eventually_eq h).symm

lemma Ioo_inter_Iio {α : Type*} [linear_order α] {a b c : α} : Ioo a b ∩ Iio c = Ioo a (min b c) :=
by { ext, simp [and_assoc] }

lemma fract_lt {x y : ℝ} {n : ℤ} (h1 : (n : ℝ) ≤ x) (h2 : x < n + y) : fract x < y :=
begin
  cases le_total y 1 with hy hy,
  { rw [← fract_sub_int x n, fract_eq_self.mpr],
    linarith,
    split; linarith },
  { exact (fract_lt_one x).trans_le hy }
end

lemma one_sub_lt_fract {x y : ℝ} {n : ℤ} (hy : y ≤ 1) (h1 : (n : ℝ) - y < x) (h2 : x < n) :
  1 - y < fract x :=
begin
  have I₁ : 1 - y < x - (n-1), by linarith,
  have I₂ : x - (n-1) < 1, by linarith,
  norm_cast at I₁ I₂,
  rw [← fract_sub_int x (n-1), fract_eq_self.mpr],
  exact I₁,
  split; linarith,
end

lemma is_open.preimage_fract' {s : set ℝ} (hs : is_open s)
  (h2s : 0 ∈ s → s ∈ 𝓝[<] (1 : ℝ)) : is_open (fract ⁻¹' s) :=
begin
  rw is_open_iff_mem_nhds,
  rintros x (hx : fract x ∈ s),
  rcases eq_or_ne (fract x)  0 with hx' | hx',
  { have H : (0 : ℝ) ∈ s, by rwa hx' at hx,
    specialize h2s H,
    rcases fract_eq_zero_iff.mp hx' with ⟨n, rfl⟩, clear hx hx',
    have s_mem_0 := hs.mem_nhds H,
    rcases (nhds_basis_zero_abs_sub_lt ℝ).mem_iff.mp s_mem_0 with ⟨δ, δ_pos, hδ⟩,
    rcases (nhds_within_has_basis (nhds_basis_Ioo_pos (1 : ℝ)) _).mem_iff.mp h2s with ⟨ε, ε_pos, hε⟩,
    rw [Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right ε_pos.le)] at hε,
    set ε' := min ε (1/2),
    have ε'_pos : 0 < ε',
      from lt_min ε_pos (by norm_num : (0 : ℝ) < 1/2),
    have hε' : Ioo (1 - ε') 1 ⊆ s,
    { apply subset.trans _ hε,
      apply Ioo_subset_Ioo_left,
      linarith [min_le_left ε (1/2)] },
    have mem : Ioo ((n : ℝ)-ε') (n+δ) ∈ 𝓝 (n : ℝ),
    { apply Ioo_mem_nhds ; linarith },
    apply mem_of_superset mem,
    rintros x ⟨hx, hx'⟩,
    cases le_or_gt (n : ℝ) x with hx'' hx'',
    { apply hδ,
      rw [mem_set_of_eq, abs_eq_self.mpr (fract_nonneg x)],
      exact fract_lt hx'' hx' },
    { apply hε',
      split,
      { refine one_sub_lt_fract (by linarith [min_le_right ε (1/2)]) (by linarith) hx'' },
      { exact fract_lt_one x }, } },
  { rw fract_ne_zero_iff at hx',
    have H : Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x,
      from mem_of_superset (Ioo_floor_mem_nhds hx') Ioo_subset_Ico_self,
    exact (continuous_on_fract ⌊x⌋).continuous_at H (hs.mem_nhds hx) },
end

lemma is_open.preimage_fract {s : set ℝ} (hs : is_open s)
  (h2s : (0 : ℝ) ∈ s → (1 : ℝ) ∈ s) : is_open (fract ⁻¹' s) :=
hs.preimage_fract' $ λ h, nhds_within_le_nhds $ hs.mem_nhds (h2s h)

-- is `sᶜ ∉ 𝓝[<] (1 : ℝ)` equivalent to something like `cluster_pt (𝓝[Iio (1 : ℝ) ∩ s] (1 : ℝ)` ?
lemma is_closed.preimage_fract {s : set ℝ} (hs : is_closed s)
  (h2s : sᶜ ∉ 𝓝[<] (1 : ℝ) → (0 : ℝ) ∈ s) : is_closed (fract ⁻¹' s) :=
is_open_compl_iff.mp $ hs.is_open_compl.preimage_fract' $ λ h, by_contra $ λ h', h $ h2s h'

lemma fract_preimage_mem_nhds {s : set ℝ} {x : ℝ} (h1 : s ∈ 𝓝 (fract x))
  (h2 : fract x = 0 → s ∈ 𝓝 (1 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x :=
begin
  by_cases hx : fract x = 0,
  { obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp h1,
    obtain ⟨v, hvs, hv, h1v⟩ := mem_nhds_iff.mp (h2 hx),
    rw [mem_nhds_iff],
    refine ⟨fract ⁻¹' (u ∪ v), preimage_mono (union_subset hus hvs),
      (hu.union hv).preimage_fract (λ _, subset_union_right _ _ h1v), subset_union_left _ _ hxu⟩ },
  { exact (continuous_at_fract hx).preimage_mem_nhds h1 }
end

end fract

section
-- to normed_space
variables {E F : Type*} [normed_add_comm_group E] [normed_add_comm_group F]
variables [normed_space ℝ E] [normed_space ℝ F]

lemma dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ unit_interval) :
  dist (r • x + (1 - r) • y) x ≤ dist y x :=
calc
  dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ : by simp_rw [dist_eq_norm', ← norm_smul,
    sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add, sub_right_comm]
  ... = (1 - r) * dist y x :
    by rw [real.norm_eq_abs, abs_eq_self.mpr (sub_nonneg.mpr h.2), dist_eq_norm']
  ... ≤ (1 - 0) * dist y x : mul_le_mul_of_nonneg_right (sub_le_sub_left h.1 _) dist_nonneg
  ... = dist y x : by rw [sub_zero, one_mul]

end

section -- to ???

-- needs classical
variables {α β γ δ ι : Type*} [topological_space α] [topological_space β] {x : α}

lemma is_open_slice_of_is_open_over {Ω : set (α × β)} {x₀ : α}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ prod.fst ⁻¹' U)) : is_open (prod.mk x₀ ⁻¹' Ω) :=
begin
  rcases hΩ_op with ⟨U, hU, hU_op⟩, convert hU_op.preimage (continuous.prod.mk x₀) using 1,
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, if_pos,
    inter_univ]
end

end

section proj_I

variables {α β : Type*} [linear_ordered_semiring α] {x c : α}

/-- If `α` is a `linear_ordered_semiring`, then `proj_I : α → α` projection of `α` onto the unit
interval `[0, 1]`. -/
def proj_I : α → α := λ x, proj_Icc (0 : α) 1 zero_le_one x

lemma proj_I_def : proj_I x = max 0 (min 1 x) := rfl

lemma proj_Icc_eq_proj_I : (proj_Icc (0 : α) 1 zero_le_one x : α) = proj_I x := rfl

lemma proj_I_of_le_zero (hx : x ≤ 0) : proj_I x = 0 :=
congr_arg coe $ proj_Icc_of_le_left _ hx

@[simp] lemma proj_I_zero : proj_I (0 : α) = 0 :=
congr_arg coe $ proj_Icc_left _

lemma proj_I_of_one_le (hx : 1 ≤ x) : proj_I x = 1 :=
congr_arg coe $ proj_Icc_of_right_le _ hx

@[simp] lemma proj_I_one : proj_I (1 : α) = 1 :=
congr_arg coe $ proj_Icc_right _

@[simp] lemma proj_I_eq_zero [nontrivial α] : proj_I x = 0 ↔ x ≤ 0 :=
by { rw [← proj_Icc_eq_left (zero_lt_one' α), subtype.ext_iff], refl }

@[simp] lemma proj_I_eq_one : proj_I x = 1 ↔ 1 ≤ x :=
by { rw [← proj_Icc_eq_right (zero_lt_one' α), subtype.ext_iff], refl }

lemma proj_I_mem_Icc : proj_I x ∈ Icc (0 : α) 1 :=
(proj_Icc (0 : α) 1 zero_le_one x).prop

lemma proj_I_eq_self : proj_I x = x ↔ x ∈ Icc (0 : α) 1 :=
⟨λ h, h ▸ proj_I_mem_Icc, λ h, congr_arg coe $ proj_Icc_of_mem _ h⟩

@[simp] lemma proj_I_proj_I : proj_I (proj_I x) = proj_I x :=
proj_I_eq_self.mpr proj_I_mem_Icc

@[simp] lemma proj_Icc_proj_I :
  proj_Icc (0 : α) 1 zero_le_one (proj_I x) = proj_Icc 0 1 zero_le_one x :=
proj_Icc_of_mem _ proj_I_mem_Icc

@[simp] lemma range_proj_I : range (proj_I) = Icc 0 1 :=
by rw [proj_I, range_comp, range_proj_Icc, image_univ, subtype.range_coe]

lemma monotone_proj_I : monotone (proj_I : α → α) :=
monotone_proj_Icc _

lemma strict_mono_on_proj_I : strict_mono_on proj_I (Icc (0 : α) 1) :=
strict_mono_on_proj_Icc _

lemma proj_I_le_max : proj_I x ≤ max 0 x :=
max_le_max le_rfl $ min_le_right _ _

lemma min_le_proj_I : min 1 x ≤ proj_I x :=
le_max_right _ _

lemma proj_I_le_iff : proj_I x ≤ c ↔ 0 ≤ c ∧ (1 ≤ c ∨ x ≤ c) :=
by simp_rw [proj_I_def, max_le_iff, min_le_iff]

@[simp] lemma proj_I_eq_min : proj_I x = min 1 x ↔ 0 ≤ x :=
by simp_rw [proj_I_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and]

lemma min_proj_I (h2 : 0 ≤ c) : min c (proj_I x) = proj_I (min c x) :=
by { cases le_total c x with h3 h3; simp [h2, h3, proj_I_le_iff, proj_I_eq_min.mpr],
     simp [proj_I_eq_min.mpr, h2.trans h3, min_left_comm c, h3] }

lemma continuous_proj_I [topological_space α] [order_topology α] :
  continuous (proj_I : α → α) :=
continuous_proj_Icc.subtype_coe

lemma proj_I_mapsto {α : Type*} [linear_ordered_semiring α] {s : set α} (h0s : (0 : α) ∈ s)
  (h1s : (1 : α) ∈ s) : maps_to proj_I s s :=
λ x hx, (le_total 1 x).elim (λ h2x, by rwa [proj_I_eq_one.mpr h2x]) $
  λ h2x, (le_total 0 x).elim (λ h3x, by rwa [proj_I_eq_self.mpr ⟨h3x, h2x⟩]) $
  λ h3x, by rwa [proj_I_eq_zero.mpr h3x]
-- about path.truncate

lemma truncate_proj_I_right {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t₀ t₁ : ℝ) (s : I) :
  γ.truncate t₀ (proj_I t₁) s = γ.truncate t₀ t₁ s :=
begin
  simp_rw [path.truncate, path.coe_mk, path.extend, Icc_extend, function.comp],
  rw [min_proj_I (s.prop.1.trans $ le_max_left _ _), proj_Icc_proj_I],
end

end proj_I

section

open encodable option
variables {α β γ : Type*} [topological_space α] [topological_space β]
-- can we restate this nicely?

/-- Given a locally finite sequence of sets indexed by an encodable type, we can naturally reindex
  this sequence to get a sequence indexed by `ℕ` (by adding some `∅` values).
  This new sequence is still locally finite. -/
lemma decode₂_locally_finite {ι} [encodable ι] {s : ι → set α}
  (hs : locally_finite s) : locally_finite (λ i, (s <$> decode₂ ι i).get_or_else ∅) :=
begin
  intro x,
  obtain ⟨U, hxU, hU⟩ := hs x,
  refine ⟨U, hxU, _⟩,
  have : encode ⁻¹' {i : ℕ | ((s <$> decode₂ ι i).get_or_else ∅ ∩ U).nonempty} =
     {i : ι | (s i ∩ U).nonempty},
  { simp_rw [preimage_set_of_eq, decode₂_encode, map_some, get_or_else_some] },
  rw [← this] at hU,
  refine finite_of_finite_preimage hU _,
  intros n hn,
  rw [← decode₂_ne_none_iff],
  intro h,
  simp_rw [mem_set_of_eq, h, map_none, get_or_else_none, empty_inter] at hn,
  exact (not_nonempty_empty hn).elim
end

open topological_space

variables {X : Type*} [emetric_space X] [locally_compact_space X] [second_countable_topology X]

lemma exists_locally_finite_subcover_of_locally {C : set X} (hC : is_closed C) {P : set X → Prop}
  (hP : antitone P) (h0 : P ∅) (hX : ∀ x ∈ C, ∃ V ∈ 𝓝 (x : X), P V) :
∃ (K : ℕ → set X) (W : ℕ → set X), (∀ n, is_compact (K n)) ∧ (∀ n, is_open (W n)) ∧
  (∀ n, P (W n)) ∧ (∀ n, K n ⊆ W n) ∧ locally_finite W ∧ C ⊆ ⋃ n, K n :=
begin
  choose V' hV' hPV' using set_coe.forall'.mp hX,
  choose V hV hVV' hcV using λ x : C, locally_compact_space.local_compact_nhds ↑x (V' x) (hV' x),
  simp_rw [← mem_interior_iff_mem_nhds] at hV,
  have : C ⊆ (⋃ x : C, interior (V x)) :=
  λ x hx, by { rw [mem_Union], exact ⟨⟨x, hx⟩, hV _⟩ },
  obtain ⟨s, hs, hsW₂⟩ := is_open_Union_countable (λ x, interior (V x)) (λ x, is_open_interior),
  rw [← hsW₂, bUnion_eq_Union] at this, clear hsW₂,
  obtain ⟨W, hW, hUW, hlW, hWV⟩ :=
    precise_refinement_set hC (λ x : s, interior (V x)) (λ x, is_open_interior) this,
  obtain ⟨K, hCK, hK, hKW⟩ :=
    exists_subset_Union_closed_subset hC (λ x : s, hW x) (λ x _, hlW.point_finite x) hUW,
  haveI : encodable s := hs.to_encodable,
  let K' : ℕ → set X := λ n, (K <$> (decode₂ s n)).get_or_else ∅,
  let W' : ℕ → set X := λ n, (W <$> (decode₂ s n)).get_or_else ∅,
  refine ⟨K', W', _, _, _, _, _, _⟩,
  { intro n, cases h : decode₂ s n with i,
    { simp_rw [K', h, map_none, get_or_else_none, is_compact_empty] },
    { simp_rw [K', h, map_some, get_or_else_some],
      exact is_compact_of_is_closed_subset (hcV i) (hK i)
        ((hKW i).trans $ (hWV i).trans interior_subset) }},
  { intro n, cases h : decode₂ s n,
    { simp_rw [W', h, map_none, get_or_else_none, is_open_empty] },
    { simp_rw [W', h, map_some, get_or_else_some, hW] }},
  { intro n, cases h : decode₂ s n with i,
    { simp_rw [W', h, map_none, get_or_else_none, h0] },
    { simp_rw [W', h, map_some, get_or_else_some], refine hP _ (hPV' i),
      refine (hWV i).trans (interior_subset.trans $ hVV' i) }},
  { intro n, cases h : decode₂ s n,
    { simp_rw [K', W', h, map_none] },
    { simp_rw [K', W', h, map_some, get_or_else_some, hKW] }},
  { exact decode₂_locally_finite hlW },
  { intros x hx, obtain ⟨i, hi⟩ := mem_Union.mp (hCK hx),
    refine mem_Union.mpr ⟨encode i, _⟩,
    simp_rw [K', decode₂_encode, map_some, get_or_else_some, hi] }
end

end

section -- to subset_properties

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]

lemma is_compact.eventually_forall_mem {x₀ : α} {K : set β} (hK : is_compact K)
  {f : α → β → γ} (hf : continuous ↿f) {U : set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
  ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
hK.eventually_forall_of_forall_eventually $ λ y hy, (hf.tendsto _).eventually $
  show U ∈ 𝓝 (↿f (x₀, y)), from hU y hy

end

section -- to separation

variables {α : Type*} [topological_space α]

/-
needs
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
-/
lemma is_open_affine_independent (𝕜 E : Type*) {ι : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [complete_space 𝕜] [finite ι] :
  is_open {p : ι → E | affine_independent 𝕜 p} :=
begin
  classical,
  cases is_empty_or_nonempty ι, { resetI, exact is_open_discrete _ },
  obtain ⟨i₀⟩ := h,
  simp_rw [affine_independent_iff_linear_independent_vsub 𝕜 _ i₀],
  let ι' := {x // x ≠ i₀},
  casesI nonempty_fintype ι,
  haveI : fintype ι' := subtype.fintype _,
  convert_to
    is_open ((λ (p : ι → E) (i : ι'), p i -ᵥ p i₀) ⁻¹' {p : ι' → E | linear_independent 𝕜 p}),
  refine is_open.preimage _ is_open_set_of_linear_independent,
  refine continuous_pi (λ i', continuous.vsub (continuous_apply i') $ continuous_apply i₀),
end

end

section convex

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E] {s : set E}

lemma convex.is_preconnected' (hs : convex ℝ s) : is_preconnected s :=
by { rcases s.eq_empty_or_nonempty with rfl|h, exact is_preconnected_empty,
     exact (hs.is_path_connected h).is_connected.is_preconnected }

end convex

section

open metric

lemma continuous.inf_dist {α β : Type*} [topological_space α] [pseudo_metric_space β] {s : set β}
  {f : α → β} (hf : continuous f) : continuous (λ x, inf_dist (f x) s) :=
(continuous_inf_dist_pt _).comp hf

end

section normed_space
open metric

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

lemma is_preconnected_ball (x : E) (r : ℝ) : is_preconnected (ball x r) :=
(convex_ball x r).is_preconnected'

lemma is_connected_ball {x : E} {r : ℝ} : is_connected (ball x r) ↔ 0 < r :=
begin
  rw [← @nonempty_ball _ _ x],
  refine ⟨λ h, h.nonempty, λ h, ((convex_ball x r).is_path_connected $ h).is_connected⟩
end

-- todo: make metric.mem_nhds_iff protected

end normed_space

section connected_component_in

variables {α β : Type*} [topological_space α] [topological_space β]

lemma continuous.image_connected_component_in_subset {f : α → β} {s : set α} {x : α}
  (hf : continuous f) (hx : x ∈ s) :
  f '' connected_component_in s x ⊆ connected_component_in (f '' s) (f x) :=
(is_preconnected_connected_component_in.image _ hf.continuous_on).subset_connected_component_in
  (mem_image_of_mem _ $ mem_connected_component_in hx)
  (image_subset _ $ connected_component_in_subset _ _)

lemma homeomorph.image_connected_component_in (f : α ≃ₜ β) {s : set α} {x : α} (hx : x ∈ s) :
  f '' connected_component_in s x = connected_component_in (f '' s) (f x) :=
begin
  refine (f.continuous.image_connected_component_in_subset hx).antisymm _,
  have := f.symm.continuous.image_connected_component_in_subset (mem_image_of_mem _ hx),
  rwa [image_subset_iff, f.preimage_symm, f.image_symm, f.preimage_image, f.symm_apply_apply]
    at this,
end


end connected_component_in

namespace topological_space -- to topology.bases
lemma cover_nat_nhds_within {α} [topological_space α] [second_countable_topology α] {f : α → set α}
  {s : set α} (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) (hs : s.nonempty) :
  ∃ x : ℕ → α, range x ⊆ s ∧ s ⊆ ⋃ n, f (x n) :=
begin
  obtain ⟨t, hts, ht, hsf⟩ := topological_space.countable_cover_nhds_within hf,
  have hnt : t.nonempty,
  { by_contra,
    rw [not_nonempty_iff_eq_empty] at h,
    rw [h, bUnion_empty, subset_empty_iff] at hsf,
    exact hs.ne_empty hsf },
  obtain ⟨x, rfl⟩ := ht.exists_eq_range hnt,
  rw [bUnion_range] at hsf,
  exact ⟨x, hts, hsf⟩
end

/-- A version of `topological_space.cover_nat_nhds_within` where `f` is only defined on `s`. -/
lemma cover_nat_nhds_within' {α} [topological_space α] [second_countable_topology α] {s : set α}
  {f : ∀ x ∈ s, set α} (hf : ∀ x (hx : x ∈ s), f x hx ∈ 𝓝[s] x) (hs : s.nonempty) :
  ∃ (x : ℕ → α) (hx : range x ⊆ s), s ⊆ ⋃ n, f (x n) (range_subset_iff.mp hx n) :=
begin
  let g := λ x, if hx : x ∈ s then f x hx else ∅,
  have hg : ∀ x ∈ s, g x ∈ 𝓝[s] x, { intros x hx, simp_rw [g, dif_pos hx], exact hf x hx },
  obtain ⟨x, hx, h⟩ := topological_space.cover_nat_nhds_within hg hs,
  simp_rw [g, dif_pos (range_subset_iff.mp hx _)] at h,
  refine ⟨x, hx, h⟩,
end

end topological_space

namespace set
namespace subtype
open _root_.subtype
variables {α : Type*}

lemma image_coe_eq_iff_eq_univ {s : set α} {t : set s} : (coe : s → α) '' t = s ↔ t = univ :=
by { convert coe_injective.image_injective.eq_iff, rw coe_image_univ }

@[simp] lemma preimage_coe_eq_univ {s t : set α} : (coe : s → α) ⁻¹' t = univ ↔ s ⊆ t :=
by rw [← inter_eq_right_iff_subset, ← image_preimage_coe, image_coe_eq_iff_eq_univ]

end subtype
end set
open set

section paracompact_space

-- a version of `precise_refinement_set` for open `s`.
/-- When `s : set X` is open and paracompact, we can find a precise refinement on `s`. Note that
 in this case we only get the locally finiteness condition on `s`, which is weaker than the local
 finiteness condition on all of `X` (the collection might not be locally finite on the boundary of
 `s`). -/
theorem precise_refinement_set' {ι X : Type*} [topological_space X] {s : set X}
  [paracompact_space s] (hs : is_open s)
  (u : ι → set X) (uo : ∀ i, is_open (u i)) (us : s ⊆ ⋃ i, u i) :
  ∃ (v : ι → set X), (∀ i, is_open (v i)) ∧ (s ⊆ ⋃ i, v i) ∧
  locally_finite (λ i, (coe : s → X) ⁻¹' v i) ∧ (∀ i, v i ⊆ s) ∧ (∀ i, v i ⊆ u i) :=
begin
  obtain ⟨v, vo, vs, vl, vu⟩ := precise_refinement (λ i, (coe : s → X) ⁻¹' u i)
    (λ i, (uo i).preimage continuous_subtype_coe)
    (by rwa [← preimage_Union, subtype.preimage_coe_eq_univ]),
  refine ⟨λ i, coe '' v i, λ i, hs.is_open_map_subtype_coe _ (vo i),
    by rw [← image_Union, vs, subtype.coe_image_univ],
    by simp_rw [preimage_image_eq _ subtype.coe_injective, vl],
    λ i, subtype.coe_image_subset _ _,
    by { intro i, rw [image_subset_iff], exact vu i }⟩,
end

lemma point_finite_of_locally_finite_coe_preimage {ι X : Type*} [topological_space X] {s : set X}
  {f : ι → set X} (hf : locally_finite (λ i, (coe : s → X) ⁻¹' f i)) (hfs : ∀ i, f i ⊆ s) {x : X} :
  {i | x ∈ f i}.finite :=
begin
  by_cases hx : x ∈ s,
  { exact hf.point_finite ⟨x, hx⟩ },
  { have : ∀ i, x ∉ f i := λ i hxf, hx (hfs i hxf),
    simp only [this, set_of_false, finite_empty] }
end


end paracompact_space

section shrinking_lemma

variables {ι X : Type*} [topological_space X]
variables {u : ι → set X} {s : set X} [normal_space s]

-- this lemma is currently formulated a little weirdly, since we have a collection of open sets
-- as the input and a collection of closed/compact sets as output.
-- Perhaps we can formulate it so that the input is a collection of compact sets whose interiors
-- cover s.
lemma exists_subset_Union_interior_of_is_open (hs : is_open s) (uo : ∀ i, is_open (u i))
  (uc : ∀ i, is_compact (closure (u i)))
  (us : ∀ i, closure (u i) ⊆ s)
  (uf : ∀ x ∈ s, {i | x ∈ u i}.finite) (uU : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ (⋃ i, interior (v i)) ∧ (∀ i, is_compact (v i)) ∧ ∀ i, v i ⊆ u i :=
begin
  obtain ⟨v, vU, vo, hv⟩ := exists_Union_eq_closure_subset
    (λ i, (uo i).preimage (continuous_subtype_coe : continuous (coe : s → X)))
    (λ x, uf x x.prop)
    (by simp_rw [← preimage_Union, subtype.preimage_coe_eq_univ, uU]),
  have : ∀ i, is_compact (closure ((coe : _ → X) '' (v i))),
  { intro i, refine is_compact_of_is_closed_subset (uc i) is_closed_closure _,
    apply closure_mono, rw image_subset_iff, refine subset_closure.trans (hv i) },
  refine ⟨λ i, closure (coe '' (v i)), _, this, _⟩,
  { refine subset.trans _ (Union_mono $
      λ i, interior_maximal subset_closure (hs.is_open_map_subtype_coe _ (vo i))),
    simp_rw [← image_Union, vU, subtype.coe_image_univ] },
  { intro i,
    have : coe '' v i ⊆ u i,
    { rintro _ ⟨x, hx, rfl⟩, exact hv i (subset_closure hx) },
    intros x hx,
    have hxs : x ∈ s := us i (closure_mono this hx),
    have : (⟨x, hxs⟩ : s) ∈ closure (v i),
    { rw embedding_subtype_coe.closure_eq_preimage_closure_image (v i), exact hx },
    exact hv i this }
end

end shrinking_lemma

open_locale filter

lemma filter.eventually_eq.slice {α β γ : Type*} [topological_space α] [topological_space β]
  {f g : α × β → γ} {a : α} {b : β} (h : f =ᶠ[𝓝 (a, b)] g) : (λ y, f (a, y)) =ᶠ[𝓝 b] (λ y, g(a, y)) :=
begin
  rw nhds_prod_eq at h,
  have : (pure a : filter α) ×ᶠ 𝓝 b ≤ (𝓝 a) ×ᶠ (𝓝 b),
  exact prod_mono (by apply pure_le_nhds) le_rfl,
  have := h.filter_mono this,
  rw [pure_prod] at this,
  exact eventually_map.mp this
end

lemma exists_compact_between' {α : Type*} [topological_space α] [locally_compact_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (h_KU : K ⊆ U) :
  ∃ L, is_compact L ∧ L ∈ 𝓝ˢ K ∧ L ⊆ U :=
let ⟨L, L_cpct, L_in, LU⟩ := exists_compact_between hK hU h_KU in
  ⟨L, L_cpct, subset_interior_iff_mem_nhds_set.mp L_in, LU⟩

section -- to topology/basic

@[simp] lemma finset.is_closed_bUnion {α} [topological_space α]
  {ι : Type*} (s : finset ι) (f : ι → set α) (hf : ∀ i ∈ s, is_closed (f i)) :
  is_closed (⋃ i ∈ s, f i) :=
is_closed_bUnion s.finite_to_set hf


end
