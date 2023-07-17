import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

variable (α : Type _) [TopologicalSpace α]

scoped[Borelize] attribute [instance] borel

theorem borelSpace_borel : @BorelSpace α _ (borel α) :=
  ⟨rfl⟩

scoped[Borelize] attribute [instance] borelSpace_borel

