import topology.constructions

variables {E F G H K : Type*} [topological_space E] [topological_space F] [topological_space G]
  [topological_space H] [topological_space K]

lemma continuous.comp₂ {g : E × F → G} (hg : continuous g) {e : H → E} (he : continuous e)
  {f : H → F} (hf : continuous f) : continuous (λ h, g (e h, f h)) :=
hg.comp $ he.prod_mk hf

lemma continuous.comp₃ {g : E × F × K → G} (hg : continuous g)
  {e : H → E} (he : continuous e) {f : H → F} (hf : continuous f)
  {k : H → K} (hk : continuous k) : continuous (λ h, g (e h, f h, k h)) :=
hg.comp₂ he $ hf.prod_mk hk
