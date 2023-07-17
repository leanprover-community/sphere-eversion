import Mathlib.Logic.Equiv.LocalEquiv

open Set

theorem LocalEquiv.range_eq_target_of_source_eq_univ {α β : Type _} (e : LocalEquiv α β)
    (h : e.source = univ) : range e = e.target := by
  rw [← image_univ, ← h, e.image_source_eq_target]
