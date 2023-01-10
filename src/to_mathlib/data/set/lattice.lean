import data.set.lattice

namespace set
variables {α β : Type*} {ι : Sort*}

-- Put next to Union_prod_const...
lemma const_prod_Union {s : ι → set α} {t : set β} : t ×ˢ (⋃ i, s i) = ⋃ i, t ×ˢ s i :=
by { ext, simp }

-- Put next to Union₂_prod_const...
lemma const_prod_Union₂ {κ : ι → Sort*} {s : Π i, κ i → set α} {t : set β} :
  t ×ˢ (⋃ i j, s i j) = ⋃ i j, t ×ˢ s i j :=
by simp_rw [const_prod_Union]

end set
