import linear_algebra.basis
import linear_algebra.dual

noncomputable theory

universe u

open function set submodule
open_locale classical big_operators

section
variables {R : Type*} [semiring R]
          {M : Type*} [add_comm_monoid M] [module R M]

def basis.flag {n : ℕ} (b : basis (fin n) R M) : fin (n + 1) → submodule R M :=
λ k, span R (b '' {j | (j : fin $ n + 1) < k })

@[simp] lemma basis.flag_zero {n : ℕ} (b : basis (fin n) R M) : b.flag 0 = ⊥ :=
begin
  simp only [basis.flag, fin.coe_eq_cast_succ],
  suffices : {j : fin n | fin.cast_succ j < 0} = ∅, by simp [this],
  ext l,
  simp [l.cast_succ.zero_le]
end

@[simp] lemma basis.flag_last {n : ℕ} (b : basis (fin n) R M) : b.flag (fin.last n) = ⊤  :=
begin
  have : {j : fin n | (j : fin $ n+1) < fin.last n} = univ,
  { ext l,
    simp [fin.cast_succ_lt_last l] },
  simp_rw [basis.flag, this],
  simp [b.span_eq]
end

attribute [mono] submodule.span_mono

@[simp] lemma basis.flag_mono {n : ℕ} (b : basis (fin n) R M) : monotone b.flag :=
begin
  intros j k h,
  dsimp [basis.flag],
  mono*,
  rintros l (hl : ↑↑l < j),
  exact lt_of_lt_of_le hl h
end

lemma fin.coe_succ_le_iff_le {n : ℕ} {j k : fin n} : (j : fin $ n+1) ≤ k ↔ j ≤ k :=
begin
  cases j,
  cases k,
  simp
end

lemma fin.coe_succ_lt_iff_lt {n : ℕ} {j k : fin n} : (j : fin $ n+1) < k ↔ j < k :=
begin
  cases j,
  cases k,
  simp
end

lemma fin.coe_lt_succ {n : ℕ} (k : fin n) : (k : fin $ n+1) < k.succ :=
begin
  cases k,
  simp
end

@[simp] lemma basis.flag_span_succ {n : ℕ} (b : basis (fin n) R M) (k : fin n) :
  b.flag k ⊔ span R {b k} = b.flag k.succ :=
begin
  rw [basis.flag, ← span_union, ← image_singleton, ← image_union],
  congr,
  ext j,
  have : j = k ∨ j < k ↔ ↑j < k.succ,
  { cases j,
    cases k,
    simp only [subtype.mk_eq_mk, subtype.mk_lt_mk, fin.coe_eq_cast_succ, fin.cast_succ_mk,
             fin.succ_mk, ← le_iff_eq_or_lt, nat.lt_succ_iff.symm] },
  simp [this]
end
end

section
variables {R : Type*} [comm_ring R]
          {M : Type*} [add_comm_group M] [module R M]

variables {n : ℕ} (b : basis (fin n) R M)

lemma basis.flag_le_ker_dual (k : fin n) : b.flag k ≤ (b.dual_basis k).ker :=
begin
  erw span_le,
  rintros _ ⟨j, hj : (j : fin $ n+1) < k, rfl⟩,
  simp [(fin.coe_succ_lt_iff_lt.mp hj).ne]
end
end
