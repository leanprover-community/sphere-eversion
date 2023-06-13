import measure_theory.constructions.borel_space.basic

variables (α : Type*) [topological_space α]

localized "attribute [instance] borel" in borelize

lemma borel_space_borel : @borel_space α _ (borel α) := ⟨rfl⟩

localized "attribute [instance] borel_space_borel" in borelize
