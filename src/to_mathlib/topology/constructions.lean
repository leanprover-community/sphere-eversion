import topology.constructions

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]
  {x : α}

lemma continuous_at.fst {f : α → β × γ} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).1) x :=
continuous_at_fst.comp hf

lemma continuous_at.snd {f : α → β × γ} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).2) x :=
continuous_at_snd.comp hf