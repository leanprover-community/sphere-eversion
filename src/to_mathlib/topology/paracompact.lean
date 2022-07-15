import topology.paracompact
import data.real.basic
import data.nat.interval

import to_mathlib.data.set.basic
import to_mathlib.data.set.finite

open_locale topological_space
open set function

/-- We could generalise and replace `ι × ℝ` with a dependent family of types but it doesn't seem
worth it. Proof partly based on `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set`. -/
lemma exists_countable_locally_finite_cover
  {ι X : Type*} [topological_space X] [t2_space X] [locally_compact_space X] [sigma_compact_space X]
  {c : ι → X} {B : ι → ℝ → set X} {p : ι → ℝ → Prop}
  (hc : surjective c)
  (hp : ∀ i r, p i r → 0 < r)
  (hp' : ∀ i r r', 0 < r → r < r' → p i r' → p i r)
  (hB₀ : ∀ i r, p i r → is_open (B i r))
  (hB₁ : ∀ i r, p i r → c i ∈ B i r)
  (hB₂ : ∀ i, (𝓝 (c i)).has_basis (p i) (B i)) :
  ∃ (s : set (ι × ℝ)),
    s.countable ∧
    (∀ z ∈ s, ↿p z) ∧
    locally_finite (↿B ∘ (coe : s → ι × ℝ)) ∧
    (⋃ z ∈ s, B (z : ι × ℝ).fst ((z : ι × ℝ).snd / 2)) = univ :=
begin
  let K' := compact_exhaustion.choice X,
  let K := K'.shiftr.shiftr,
  let C : ℕ → set X := λ n, K (n + 2) \ interior (K (n + 1)),
  let U : ℕ → set X := λ n, interior (K (n + 3)) \ K n,
  have hCU : ∀ n, C n ⊆ U n := λ n x hx,
    ⟨K.subset_interior_succ _ hx.1, mt (λ hx₃, K.subset_interior_succ _ hx₃) hx.2⟩,
  have hC : ∀ n, is_compact (C n) := λ n, (K.is_compact _).diff is_open_interior,
  have hC' : (⋃ n, C n) = univ,
  { refine set.univ_subset_iff.mp (λ x hx, mem_Union.mpr ⟨K'.find x, _⟩),
    simpa only [K'.find_shiftr]
      using diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x), },
  have hU : ∀ n, is_open (U n) := λ n,
    is_open_interior.sdiff $ is_compact.is_closed $ K.is_compact _,
  have hU' : ∀ n, { m | (U m ∩ U n).nonempty }.finite := λ n, by
  { suffices : {m | (U m ∩ U n).nonempty} ⊆ Icc (n-2) (n+2), { exact (finite_Icc _ _).subset this },
    rintros m ⟨x, ⟨⟨hx₁, hx₂⟩, ⟨hx₃, hx₄⟩⟩⟩,
    simp only [mem_Icc, tsub_le_iff_right],
    suffices : ∀ {a b : ℕ}, x ∉ K a → x ∈ interior (K b.succ) → a ≤ b,
    { exact ⟨this hx₄ hx₁, this hx₂ hx₃⟩, },
    intros a b ha hb,
    by_contra hab,
    replace hab : b + 1 ≤ a, { simpa using hab, },
    exact set.nonempty.ne_empty (⟨x, interior_subset hb, ha⟩ : (K b.succ \ K a).nonempty)
        (set.diff_eq_empty.mpr (K.subset hab)), },
  have hU'' : ∀ n x, x ∈ C n → U n ∈ 𝓝 x := λ n x hx,
    mem_nhds_iff.mpr ⟨U n, subset.rfl, hU n, hCU n hx⟩,
  have : ∀ n (x : C n), ∃ i r, ↑x ∈ B i (r/2) ∧ B i r ⊆ U n ∧ p i r,
  { rintros n ⟨x, hx⟩,
    obtain ⟨i, rfl⟩ := hc x,
    obtain ⟨r, hr₁, hr₂⟩ := (hB₂ i).mem_iff.mp (hU'' n _ hx),
    have hr₃ : 0 < r := hp i r hr₁,
    exact ⟨i, r, hB₁ i _ (hp' i (r/2) r (half_pos hr₃) (half_lt_self hr₃) hr₁), hr₂, hr₁⟩, },
  choose i r h₁ h₂ h₃ using λ n, this n,
  have hr : ∀ n (x : C n), 0 < r n x := λ n x, hp _ _ (h₃ n x),
  have hpr : ∀ n (x : C n), p (i n x) (r n x / 2) :=
    λ n x, hp' (i n x) _ _ (half_pos (hr n x)) (half_lt_self (hr n x)) (h₃ n x),
  let V : Π n, C n → set X := λ n x, B (i n x) (r n x / 2),
  have hV₁ : ∀ n x, is_open (V n x) := λ n x, hB₀ _ _ (hpr n x),
  have hV₂ : ∀ n, C n ⊆ ⋃ (x : C n), V n x := λ n x hx, mem_Union.mpr ⟨⟨x, hx⟩, h₁ _ _⟩,
  choose f hf using λ n, (hC n).elim_finite_subcover (V n) (hV₁ n) (hV₂ n),
  classical,
  let s : set (ι × ℝ) := ⋃ n, (f n).image (pi.prod (i n) (r n)),
  refine ⟨s, countable_Union (λ n, finset.countable_to_set _), λ z hz, _, λ x, _,
    set.univ_subset_iff.mp (λ x hx, _)⟩,
  { simp only [pi.prod, mem_Union, finset.coe_image, mem_image, finset.mem_coe, set_coe.exists]
      at hz,
    obtain ⟨n, x, hx, -, rfl⟩ := hz,
    apply h₃, },
  { obtain ⟨n, hn⟩ := Union_eq_univ_iff.mp hC' x,
    refine ⟨U n, hU'' n x hn, _⟩,
    let P : ι × ℝ → Prop := λ z, (↿B (z : ι × ℝ) ∩ U n).nonempty,
    rw (set.subsubset_equiv_inter s P).set_finite_iff,
    simp only [s, P, set.Union_inter],
    refine set.finite_Union' (λ m, set.to_finite _) (hU' n) (λ m hm, _),
    rw set.eq_empty_iff_forall_not_mem,
    intros z,
    simp only [pi.prod, finset.coe_image, mem_inter_eq, mem_image, finset.mem_coe, set_coe.exists,
      mem_set_of_eq, not_and, bex_imp_distrib, and_imp],
    rintros x hx₁ hx₂ rfl,
    rw set.not_nonempty_iff_eq_empty,
    have := set.inter_subset_inter_left (U n) (h₂ m ⟨x, hx₁⟩),
    rwa [set.not_nonempty_iff_eq_empty.mp hm, set.subset_empty_iff] at this, },
  { obtain ⟨n, hn⟩ := Union_eq_univ_iff.mp hC' x,
    specialize hf n hn,
    simp only [Union_coe_set, mem_Union, exists_prop] at hf,
    obtain ⟨y, hy₁, hy₂, hy₃⟩ := hf,
    simp only [pi.prod, mem_Union, finset.mem_coe, finset.mem_image, exists_prop, set_coe.exists,
      Union_exists, exists_and_distrib_right, prod.exists, prod.mk.inj_iff],
    exact ⟨i n ⟨y, hy₁⟩, r n ⟨y, hy₁⟩, ⟨n, y, hy₁, hy₂, rfl, rfl⟩, hy₃⟩, },
end
