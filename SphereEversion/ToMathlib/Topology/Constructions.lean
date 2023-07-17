import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyFinite

open Set Function Filter

open scoped Topology Filter

universe u

variable {ι : Type u} {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- This needs to go into topology.constructions which imports locally_finite and defines the
-- product topology.
theorem LocallyFinite.prod_right {f : ι → Set X} (hf : LocallyFinite f) (g : ι → Set Y) :
    LocallyFinite fun i => f i ×ˢ g i := by
  rintro ⟨x, y⟩
  rcases hf x with ⟨U, U_in, hU⟩
  refine' ⟨U ×ˢ univ, prod_mem_nhds U_in univ_mem, _⟩
  apply finite.subset hU
  rintro i ⟨⟨x', y'⟩, ⟨⟨H, -⟩, ⟨H', -⟩⟩⟩
  exact ⟨x', H, H'⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem LocallyFinite.prod_left {f : ι → Set X} (hf : LocallyFinite f) (g : ι → Set Y) :
    LocallyFinite fun i => g i ×ˢ f i := by
  rintro ⟨y, x⟩
  rcases hf x with ⟨U, U_in, hU⟩
  refine' ⟨univ ×ˢ U, prod_mem_nhds univ_mem U_in, _⟩
  apply finite.subset hU
  rintro i ⟨⟨y', x'⟩, ⟨⟨-, H⟩, ⟨-, H'⟩⟩⟩
  exact ⟨x', H, H'⟩

