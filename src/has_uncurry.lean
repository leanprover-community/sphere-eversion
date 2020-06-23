/-!
Recursive and unbundling uncurry, by Gabriel Ebner.

This should go to mathlib ASAP.
-/

section uncurry
open function

variables {α β γ δ : Type*}

example (f : α → β → γ → δ) : (α × β) × γ → δ :=
(uncurry ∘ uncurry) f 

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. -/
class has_uncurry (α : Type*) (β : out_param Type*) (γ : out_param Type*) := (uncurry : α → (β → γ))

notation `↿`:max x:max := has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ := 
⟨λ f p, ↿(f p.1) p.2⟩

variables (f : α → β → γ) (g : α → β → γ → δ)

example (a : α) (b : β) :  ↿f (a, b)=  f a b := rfl

example (a : α) (b : β) (c : γ) :  ↿g (a, b, c)=  g a b c := rfl

example :  ↿f = uncurry f := funext (λ _, rfl)

end uncurry
