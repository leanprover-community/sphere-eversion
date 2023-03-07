import order.filter.basic

lemma filter.eventually_eq.eventually_eq_ite {X Y : Type*} {l : filter X} {f g : X → Y}
  {P : X → Prop} [decidable_pred P] (h : f =ᶠ[l] g) :
(λ x, if P x then f x else g x) =ᶠ[l] f :=
begin
  apply h.mono (λ x hx, _),
  dsimp only,
  split_ifs ; tauto
end
