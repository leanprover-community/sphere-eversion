import topology.instances.real

/-!
# Gluing continuous functions

These are preliminaries about gluing continuous functions that should be in mathlib
in some form.
I also let a couple of lemmas that I ended up not using but should still be somewhere.
-/

noncomputable theory
open_locale classical topological_space filter
open filter set 

lemma tendsto_nhds_within_of_tendsto_of_subset {α β : Type*} [topological_space α] [topological_space β] {s : set α} {t : set β} 
{f : α → β} {x : α} {y : β}  (h : tendsto f (𝓝 x) (𝓝 y)) (h' : s ⊆ f ⁻¹' t) :
  tendsto f (nhds_within x s) (nhds_within y t) :=
begin
  erw tendsto_inf,
  split,
  { exact tendsto_nhds_within_of_tendsto_nhds h },
  { apply tendsto_inf_right,
    rwa tendsto_principal_principal },
end

lemma tendsto_nhds_within_of_not_in_closure {α β : Type*} [topological_space α] {s : set α} 
{f : α → β} {x : α} {F : filter β}  (h : x ∉ closure s) :
  tendsto f (nhds_within x s) F :=
begin
  rw mem_closure_iff_nhds_within_ne_bot at h,
  simp at h,
  simp [h],
end

section
variables {α : Type*}
lemma Icc_inter_Icc_subset {α : Type*} [preorder α] (a b c : α) : Icc a b ∩ Iic c ⊆ Icc a c :=
begin
  rintros x ⟨⟨xa, xb⟩, h⟩,
  split ; assumption,
end

lemma Icc_inter_Icc {a b c : α} [semilattice_inf α] : Icc a b ∩ Iic c = Icc a (b ⊓ c) :=
begin
  ext x,
  simp [and_assoc]
end

lemma Icc_inter_Ici_subset {α : Type*} [preorder α] (a b c : α) : Icc a b ∩ Ici c ⊆ Icc c b :=
begin
  rintros x ⟨⟨ax, xb⟩, xc⟩,
  split ; assumption,
end

lemma Icc_inter_Ici {α : Type*} [semilattice_sup α] {a b c : α} : Icc a b ∩ Ici c = Icc (a ⊔ c) b :=
begin
  ext x,
  change (a ≤ x ∧ x ≤ b) ∧ c ≤ x ↔ a ⊔ c ≤ x ∧ x ≤ b,
  simp,
  tauto
end

attribute [simp] Ici_inter_Iic

end

lemma and_iff_and_of_imp_iff {p q r : Prop} (h : r → (p ↔ q)) : (p ∧ r) ↔ (q ∧ r) :=
by tauto

local notation `cl` := closure

lemma continuous_on_if_aux {α β : Type*} [topological_space α] {p : α → Prop} {s : set α} {f g : α → β}
  (hp : ∀ (a : α), a ∈ s ∩ frontier p → f a = g a) (t : set β) :
  (λ a, if p a then f a else g a) ⁻¹' t ∩ s ∩ cl p = f ⁻¹' t ∩ s ∩ cl p :=
begin
  let φ : α → β := λ (a : α), ite (p a) (f a) (g a),
  let A : set α := {a : α | p a},
  have : ∀ x ∈ s ∩ cl A, φ x = f x,
  { rintros x ⟨xs, xA⟩,
    rw closure_eq_self_union_frontier A at xA,
    cases xA,
    { change p x at xA,
      simp [φ, if_pos xA] },
    { specialize hp x ⟨xs, xA⟩,
      dsimp [φ],
      split_ifs ; tauto } },
    ext x,
  rw [inter_assoc, mem_inter_iff],
  conv_rhs { rw [inter_assoc, mem_inter_iff] },
  apply and_iff_and_of_imp_iff,
  intro x_in,
  change φ x ∈ _ ↔ f x ∈ _,
  rw this x x_in,
end

lemma continuous_on_if {α β : Type*} [topological_space α] [topological_space β] {p : α → Prop} {s : set α}
  {f g : α → β} 
  (hp : ∀ a ∈ s ∩ frontier p, f a = g a) (hf : continuous_on f $ s ∩ closure p)
  (hg : continuous_on g $ s ∩ closure pᶜ) :
  continuous_on (λ a, if p a then f a else g a) s :=
begin
  set φ := (λ a, if p a then f a else g a),
  set A := {a | p a},
  set B := {a | ¬ p a},
  rw continuous_on_iff_is_closed at *,
  intros t t_closed,
  rcases hf t t_closed with ⟨u, u_closed, hu⟩,
  rcases hg t t_closed with ⟨v, v_closed, hv⟩,
  use [(u ∩ cl A) ∪ (v ∩ cl B),
       is_closed_union (is_closed_inter u_closed is_closed_closure) 
                       (is_closed_inter v_closed  is_closed_closure)],
  have factA : φ ⁻¹' t ∩ s ∩ cl A = f ⁻¹' t ∩ s ∩ cl A := continuous_on_if_aux hp t,
  have factB : φ ⁻¹' t ∩ s ∩ cl B = g ⁻¹' t ∩ s ∩ cl B,
  { rw show φ = (λ a, if pᶜ a then g a else f a), by { ext a, dsimp [φ], split_ifs ; refl },
    have hp' : ∀ a ∈ s ∩ frontier pᶜ, g a = f a, by simpa [frontier_compl, eq_comm] using hp,
    convert continuous_on_if_aux hp' t, ext a, convert rfl, },
  have cl_cl : cl A ∪ cl B = univ,
  { apply eq_univ_of_subset _ (union_compl_self $ set_of p),
    exact union_subset_union subset_closure subset_closure },
  calc φ ⁻¹' t ∩ s = (φ ⁻¹' t ∩ s) ∩ (cl A ∪ cl B) : by simp [cl_cl]
  ... = φ ⁻¹' t ∩ s ∩ cl A ∪ φ ⁻¹' t ∩ s ∩ cl B  : by rw inter_union_distrib_left
  ... = f ⁻¹' t ∩ s ∩ cl A ∪ g ⁻¹' t ∩ s ∩ cl B  : by rw [factA, factB]
  ... = (u ∩ s ∩ cl A) ∪ (v ∩ s ∩ cl B) : by assoc_rewrite [hu, hv]
  ... =  (u ∩ cl A ∪ v ∩ cl B) ∩ s : by rw [inter_right_comm, inter_right_comm v, union_inter_distrib_right],
end

lemma continuous_on_if_Icc {α β : Type*} [topological_space α] [linear_order α] [order_topology α] [densely_ordered α] [no_top_order α] [topological_space β] {a b c : α} {f g : α → β} 
  (hf : continuous_on f $ Icc a b) (hg : continuous_on g $ Icc b c) (hb : f b = g b) :
  continuous_on (λ x, if x ≤ b then f x else g x) (Icc a c) :=
begin
  apply continuous_on_if,
  { erw frontier_Iic,
    rintros x ⟨_, x_in⟩,
    convert hb },
  { erw is_closed_Iic.closure_eq,
    exact continuous_on.mono hf (Icc_inter_Icc_subset _ _ _),
    apply_instance },
  { change continuous_on g ((Icc a c) ∩ cl {a | ¬ a ≤ b}),
    push_neg,
    erw closure_Ioi,
    exact continuous_on.mono hg (Icc_inter_Ici_subset _ _ _) }
end
