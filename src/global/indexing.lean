import tactic.linarith
import topology.basic

/-!
# Indexing types

This is a stupid file introducing a type class for types that will index
locally finite covers of (paracompact) manifolds without having
to discuss according to compactness. The only intended instances
are `ℕ` and `fin (n+1)`.

It also includes a lemma about locally finite cover that doesn't require an indexing
index type but will be used with one.
-/

class indexing (α : Type*) [linear_order α] :=
(from_nat : ℕ → α)
(to_nat : α → ℕ)
(mono_from : monotone from_nat)
(from_to : ∀ a, from_nat (to_nat a) = a)

instance indexing.has_coe (α : Type*) [linear_order α] [indexing α] : has_coe ℕ α :=
⟨indexing.from_nat⟩

instance : indexing ℕ :=
{ from_nat := id,
  to_nat := id,
  mono_from := monotone_id,
  from_to := λ n, rfl }

instance (n : ℕ) : indexing (fin $ n + 1) :=
{ from_nat := λ k, if h : k < n + 1 then ⟨k, h⟩ else fin.last n,
  to_nat := coe,
  mono_from := λ k l hkl, begin
    dsimp [fin.of_nat],
    split_ifs ; try { simp [fin.le_last] };
    linarith,
  end,
  from_to := begin
    rintros ⟨k, hk⟩,
    erw dif_pos hk,
    refl
  end }

open_locale topological_space

lemma foo {X : Type*} [topological_space X] {ι : Type*} [linear_order ι] [nonempty ι]
  {s : ι → set X} (h : locally_finite s) :
  ∃ ind : X → ι, ∃ U : X → set X, ∀ x, U x ∈ 𝓝 x ∧ ∀ i > ind x, s i ∩ U x = ∅ :=
begin
  choose V V_in hV using h,
  choose ind hind using (λ x, (hV x).bdd_above),
  refine ⟨ind, V, λ  x, ⟨V_in x, _⟩⟩,
  intros i hi,
  by_contra,
  exact lt_irrefl i (gt_of_gt_of_ge hi $ hind x (set.ne_empty_iff_nonempty.mp h))
end

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `fin n` otherwise-/
def index_type (n : ℕ) : Type :=
nat.cases_on n ℕ (λ k, fin $ k + 1)

instance (n : ℕ) : linear_order (index_type n) :=
nat.cases_on n nat.linear_order (λ _, fin.linear_order)

instance (n : ℕ) : indexing (index_type n) :=
nat.cases_on n nat.indexing (λ _, fin.indexing _)
