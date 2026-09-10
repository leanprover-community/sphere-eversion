module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

public section

variable (X : Type*) [TopologicalSpace X]

scoped[Borelize] attribute [instance] borel

theorem borelSpace_borel : @BorelSpace X _ (borel X) :=
  letI := borel X; ⟨rfl⟩

scoped[Borelize] attribute [instance] borelSpace_borel
