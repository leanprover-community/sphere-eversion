import measure_theory.measure.measure_space
import measure_theory.constructions.borel_space
import measure_theory.integral.bochner

open topological_space (second_countable_topology)
open measure_theory set classical filter

open_locale classical topological_space filter interval

variables {α β E F : Type*} [measurable_space α] {μ : measure α} [normed_add_comm_group E]
          [complete_space E] [normed_space ℝ E]

namespace measure_theory
lemma ae_restrict_eq_iff {s : set α} {f g : α → β} (h : measurable_set {x | f x = g x}) :
  f =ᵐ[μ.restrict s] g ↔ ∀ᵐ x ∂μ, x ∈ s → f x = g x :=
ae_restrict_iff h

/-
MOVE next to ae_restrict_of_ae_restrict_of_subset
-/
lemma ae_mem_imp_of_ae_restrict_of_subset {α : Type*} {m0 : measurable_space α}
  {μ : measure α} {s t : set α} {p : α → Prop} (hst : s ⊆ t) (hp : ∀ᵐ (x : α) ∂μ.restrict t, p x) :
  (∀ᵐ x ∂μ, x ∈ s → p x) :=
ae_imp_of_ae_restrict (ae_restrict_of_ae_restrict_of_subset hst hp)
end measure_theory

lemma ae_restrict_of_forall_mem {α : Type*} [measurable_space α] {μ : measure α} {s : set α}
  {p : α → Prop} (hs : measurable_set s) (h : ∀ x ∈ s, p x) : ∀ᵐ (x : α) ∂μ.restrict s, p x :=
by { rw ae_restrict_iff' hs, exact ae_of_all _ h }

open measure_theory

lemma ae_interval_oc {ν : measure ℝ} {P : ℝ → Prop} {a b : ℝ} :
  (∀ᵐ t ∂(ν.restrict $ Ι a b), P t) ↔
  (∀ᵐ t ∂(ν.restrict $ Ioc a b), P t) ∧ ∀ᵐ t ∂(ν.restrict $ Ioc b a), P t :=
begin
  cases le_or_lt a b with h h,
  { simp [interval_oc_of_le h, Ioc_eq_empty_of_le h] },
  { simp [interval_oc_of_lt h, Ioc_eq_empty_of_le h.le] }
end

lemma is_compact.integrable_const {α : Type*} [measurable_space α] [topological_space α]
  {E : Type*} [normed_add_comm_group E] [measurable_space E]
  {s : set α} (hs : is_compact s) (c : E) (μ : measure α) [is_locally_finite_measure μ] :
  integrable (λ (x : α), c) (μ.restrict s) :=
by simp_rw [integrable_const_iff, measure.restrict_apply_univ, hs.measure_lt_top, or_true]
