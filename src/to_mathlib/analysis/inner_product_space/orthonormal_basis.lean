/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.pi_L2

variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]

open finite_dimensional function

-- move to `finset.card` or maybe track it down in the library
lemma finset.exists_equiv_extend_of_card_eq {α β : Type*} [fintype α] [decidable_eq β] {t : finset β}
  (hαt : fintype.card α = t.card) {s : finset α} :
  ∀ {f : α → β} (hfst : s.image f ⊆ t) (hfs : set.inj_on f s),
    ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i :=
begin
  classical,
  apply @finset.induction α
    (λ s, ∀ f (hfst : s.image f ⊆ t) (hfs : set.inj_on f s), ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i),
  { intros f hfst hfs,
    have : nonempty (α ≃ ↥t) := by rwa [← fintype.card_eq, fintype.card_coe],
    use this.some,
    simp },
  intros a s has H f hfst hfs,
  have hfst' : finset.image f s ⊆ t := (finset.image_mono _ (s.subset_insert a)).trans hfst,
  have hfs' : set.inj_on f s := hfs.mono (s.subset_insert a),
  obtain ⟨g', hg'⟩ := H f hfst' hfs',
  have hfat : f a ∈ t := hfst (finset.mem_image_of_mem _ (s.mem_insert_self a)),
  use g'.trans (equiv.swap (⟨f a, hfat⟩ : t) (g' a)),
  intros i hi,
  obtain rfl | his : i = a ∨ i ∈ s := by simpa using hi,
  { simp },
  simp only [equiv.coe_trans, comp_app],
  rw equiv.swap_apply_of_ne_of_ne,
  { rw hg' i his },
  { intros h,
    apply has,
    have h' : f i = f a := by simpa only [subtype.ext_iff, hg' i his, subtype.coe_mk] using h,
    rw ← hfs (finset.mem_coe.mpr hi) (s.mem_insert_self a) h',
    exact his },
  { apply g'.injective.ne,
    rintros rfl,
    contradiction }
end

-- move to `finset.card` or maybe track it down in the library
lemma finset.exists_equiv_extend_of_card_eq' {α β : Type*} [fintype α] {t : finset β}
  (hαt : fintype.card α = t.card) {s : set α} {f : α → β} (hfst : f '' s ⊆ t)
  (hfs : set.inj_on f s) :
  ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i :=
begin
  classical,
  let s' : finset α := s.to_finset,
  have hfst' : s'.image f ⊆ t := by simpa [← finset.coe_subset] using hfst,
  have hfs' : set.inj_on f s' := by simpa using hfs,
  obtain ⟨g, hg⟩ := finset.exists_equiv_extend_of_card_eq hαt hfst' hfs',
  refine ⟨g, λ i hi, _⟩,
  apply hg,
  simpa using hi,
end

-- `analysis.inner_product_space.basic`
lemma orthonormal_subtype_range {ι : Type*} {f : ι → E} (hf : function.injective f) :
  orthonormal 𝕜 (coe : set.range f → E) ↔ orthonormal 𝕜 f :=
begin
  let F : ι ≃ set.range f := equiv.of_injective f hf,
  refine ⟨λ h, h.comp F F.injective, λ h, _⟩,
  rw ← equiv.self_comp_of_injective_symm hf,
  exact h.comp F.symm F.symm.injective,
end

-- `analysis.inner_product_space.pi_L2`
lemma orthonormal.exists_orthonormal_basis_extension_of_card_eq [finite_dimensional 𝕜 E]
  {ι : Type*} [fintype ι] (card_ι : finrank 𝕜 E = fintype.card ι) {v : ι → E} {s : set ι}
  (hv : orthonormal 𝕜 (s.restrict v)) :
  ∃ b : orthonormal_basis ι 𝕜 E, ∀ i ∈ s, b i = v i :=
begin
  have hsv : injective (s.restrict v) := hv.linear_independent.injective,
  have hX : orthonormal 𝕜 (coe : set.range (s.restrict v) → E),
  { rwa orthonormal_subtype_range hsv },
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormal_basis_extension,
  have hιY : fintype.card ι = Y.card,
  { refine (card_ι.symm.trans _),
    exact finite_dimensional.finrank_eq_card_finset_basis b₀.to_basis },
  have hvsY : v '' s ⊆ Y,
  { rintros - ⟨i, hi, rfl⟩,
    exact hX ⟨⟨i, hi⟩, rfl⟩ },
  have hsv' : set.inj_on v s,
  { rw set.inj_on_iff_injective,
    exact hsv },
  obtain ⟨g, hg⟩ := finset.exists_equiv_extend_of_card_eq' hιY hvsY hsv',
  use b₀.reindex g.symm,
  intros i hi,
  { simp [hb₀, hg i hi] },
end
