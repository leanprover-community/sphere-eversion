import order.filter.at_top_bot

open filter

/- Move next to `eventually_gt_at_top` in `at_top_bot.lean` -/
lemma eventually_ne_at_top {α : Type*} [preorder α] [no_max_order α] (a : α) :
  ∀ᶠ x in at_top, x ≠ a :=
(eventually_gt_at_top a).mono (λ x hx, hx.ne.symm)
