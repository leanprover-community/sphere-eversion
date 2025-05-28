import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped Topology

open Set Function

/-- We could generalise and replace `ι × ℝ` with a dependent family of types but it doesn't seem
worth it. Proof partly based on `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`. -/
theorem exists_countable_locallyFinite_cover {ι X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SigmaCompactSpace X] {c : ι → X} {W : ι → ℝ → Set X}
    {B : ι → ℝ → Set X} {p : ι → ℝ → Prop} (hc : Surjective c) (hW₀ : ∀ i r, p i r → c i ∈ W i r)
    (hW₁ : ∀ i r, p i r → IsOpen (W i r)) (hB : ∀ i, (𝓝 (c i)).HasBasis (p i) (B i)) :
    ∃ s : Set (ι × ℝ), s.Countable ∧ (∀ z ∈ s, (↿p) z) ∧ (⋃ z ∈ s, (↿W) z) = univ ∧
      LocallyFinite (↿B ∘ ((↑) : s → ι × ℝ)) := by
  let K' := CompactExhaustion.choice X
  let K := K'.shiftr.shiftr
  let C : ℕ → Set X := fun n ↦ K (n + 2) \ interior (K (n + 1))
  let U : ℕ → Set X := fun n ↦ interior (K (n + 3)) \ K n
  have hCU : ∀ n, C n ⊆ U n := fun n x hx ↦
    ⟨K.subset_interior_succ _ hx.1, mt (fun hx₃ ↦ K.subset_interior_succ _ hx₃) hx.2⟩
  have hC : ∀ n, IsCompact (C n) := fun n ↦ (K.isCompact _).diff isOpen_interior
  have hC' : (⋃ n, C n) = univ := by
    refine Set.univ_subset_iff.mp fun x _ ↦ mem_iUnion.mpr ⟨K'.find x, ?_⟩
    simpa only [K'.find_shiftr] using
      diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x)
  have hU : ∀ n, IsOpen (U n) := fun n ↦
    isOpen_interior.sdiff <| IsCompact.isClosed <| K.isCompact _
  have hU' : ∀ n, {m | (U m ∩ U n).Nonempty}.Finite := fun n ↦ by
    suffices {m | (U m ∩ U n).Nonempty} ⊆ Icc (n - 2) (n + 2) by exact (finite_Icc _ _).subset this
    rintro m ⟨x, ⟨⟨hx₁, hx₂⟩, ⟨hx₃, hx₄⟩⟩⟩
    simp only [mem_Icc, tsub_le_iff_right]
    suffices ∀ {a b : ℕ}, x ∉ K a → x ∈ interior (K b.succ) → a ≤ b by
      exact ⟨this hx₄ hx₁, this hx₂ hx₃⟩
    intro a b ha hb
    by_contra hab
    replace hab : b + 1 ≤ a := by simpa using hab
    exact Set.Nonempty.ne_empty (⟨x, interior_subset hb, ha⟩ : (K b.succ \ K a).Nonempty)
      (Set.diff_eq_empty.mpr (K.subset hab))
  have hU'' : ∀ n x, x ∈ C n → U n ∈ 𝓝 x := fun n x hx ↦
    mem_nhds_iff.mpr ⟨U n, Subset.rfl, hU n, hCU n hx⟩
  have : ∀ (n) (x : C n), ∃ i r, ↑x ∈ W i r ∧ B i r ⊆ U n ∧ p i r := fun n ⟨x, hx⟩ ↦ by
    obtain ⟨i, rfl⟩ := hc x
    obtain ⟨r, hr₁, hr₂⟩ := (hB i).mem_iff.mp (hU'' n _ hx)
    exact ⟨i, r, hW₀ i r hr₁, hr₂, hr₁⟩
  choose i r h₁ h₂ h₃ using fun n ↦ this n
  let V : ∀ n, C n → Set X := fun n x ↦ W (i n x) (r n x)
  have hV₁ : ∀ n x, IsOpen (V n x) := fun n x ↦ hW₁ _ _ (h₃ n x)
  have hV₂ : ∀ n, C n ⊆ ⋃ x : C n, V n x := fun n x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, h₁ _ _⟩
  choose f hf using fun n ↦ (hC n).elim_finite_subcover (V n) (hV₁ n) (hV₂ n)
  classical
  let s : Set (ι × ℝ) := ⋃ n, (f n).image (Pi.prod (i n) (r n))
  refine ⟨s, countable_iUnion fun n ↦ Finset.countable_toSet _, fun z hz ↦ ?_,
    Set.univ_subset_iff.mp fun x _ ↦ ?_, fun x ↦ ?_⟩
  · simp only [Pi.prod, mem_iUnion, Finset.coe_image, mem_image, Finset.mem_coe,
      SetCoe.exists, s] at hz
    obtain ⟨n, x, hx, -, rfl⟩ := hz
    apply h₃
  · obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hC' x
    specialize hf n hn
    simp only [iUnion_coe_set, mem_iUnion, exists_prop] at hf
    obtain ⟨y, hy₁, hy₂, hy₃⟩ := hf
    simp only [Pi.prod, mem_iUnion, Finset.mem_coe, Finset.mem_image, exists_prop, SetCoe.exists,
      iUnion_exists, exists_and_right, Prod.exists, Prod.mk_inj, s]
    exact ⟨i n ⟨y, hy₁⟩, r n ⟨y, hy₁⟩, ⟨n, y, hy₁, hy₂, rfl, rfl⟩, hy₃⟩
  · obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hC' x
    refine ⟨U n, hU'' n x hn, ?_⟩
    let P : ι × ℝ → Prop := fun z ↦ ((↿B) (z : ι × ℝ) ∩ U n).Nonempty
    erw [(Equiv.Set.sep s P).symm.set_finite_iff]
    simp only [Set.iUnion_inter, ← inter_setOf_eq_sep, s]
    refine  (hU' n).iUnion (fun m _ ↦ Set.toFinite _) fun m hm ↦ ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro z
    simp only [Pi.prod, Finset.coe_image, mem_inter_iff, mem_image, Finset.mem_coe, SetCoe.exists,
      mem_setOf_eq, not_and, exists₂_imp, and_imp]
    rintro x hx₁ - rfl
    rw [Set.not_nonempty_iff_eq_empty]
    have := Set.inter_subset_inter_left (U n) (h₂ m ⟨x, hx₁⟩)
    rwa [Set.not_nonempty_iff_eq_empty.mp hm, Set.subset_empty_iff] at this
