/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import linear_algebra.orientation
import to_mathlib.linear_algebra.determinant


variables {R : Type*} [linear_ordered_comm_ring R] {M : Type*}
  [add_comm_group M] [module R M] {ι : Type*} [decidable_eq ι] [fintype ι]

lemma basis.det_adjust_to_orientation [nontrivial R] [nonempty ι] (e : basis ι R M)
  (x : orientation R M ι) :
  (e.adjust_to_orientation x).det = e.det ∨ (e.adjust_to_orientation x).det = - e.det :=
begin
  dsimp [basis.adjust_to_orientation],
  split_ifs,
  { left,
    refl },
  { right,
    simp [e.det_units_smul', ← units.coe_prod, finset.prod_update_of_mem] }
end

lemma basis.abs_det_adjust_to_orientation [nontrivial R] [nonempty ι] (e : basis ι R M)
  (x : orientation R M ι) (v : ι → M) :
  |(e.adjust_to_orientation x).det v| = |e.det v| :=
begin
  cases e.det_adjust_to_orientation x with h h;
  simp [h]
end
