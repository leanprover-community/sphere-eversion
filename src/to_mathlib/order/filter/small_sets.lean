import to_mathlib.data.real_basic
import to_mathlib.misc
import analysis.normed.group.basic

open_locale filter topological_space
open filter set metric

variables {α ι : Type*}

def filter.small_sets (f : filter α) : filter (set α) :=
⨅ t ∈ f, 𝓟 {s | s ⊆ t}

lemma filter.has_basis_small_sets (f : filter α) :
  has_basis f.small_sets (λ t : set α, t ∈ f) (λ t, {s | s ⊆ t}) :=
begin
  apply has_basis_binfi_principal _ _,
  { rintros u (u_in : u ∈ f) v (v_in : v ∈ f),
    use [u ∩ v, inter_mem u_in v_in],
    split,
    rintros w (w_sub : w ⊆ u ∩ v),
    exact w_sub.trans (inter_subset_left u v),
    rintros w (w_sub : w ⊆ u ∩ v),
    exact w_sub.trans (inter_subset_right u v) },
  { use univ,
    exact univ_mem },
end

lemma filter.has_basis.small_sets {f : filter α} {p : ι → Prop} {s : ι → set α}
  (h : has_basis f p s) : has_basis f.small_sets p (λ i, {u | u ⊆ s i}) :=
⟨begin
  intros t,
  rw f.has_basis_small_sets.mem_iff,
  split,
  { rintro ⟨u, u_in, hu : {v : set α | v ⊆ u} ⊆ t⟩,
    rcases h.mem_iff.mp u_in with ⟨i, hpi, hiu⟩,
    use [i, hpi],
    apply subset.trans _ hu,
    intros v hv x hx,
    exact hiu (hv hx) },
  { rintro ⟨i, hi, hui⟩,
    exact ⟨s i, h.mem_of_mem hi, hui⟩ }
end⟩

-- sanity check
example {κ : Type*} {a : filter κ} {f : filter α} {g : κ → set α} :
  tendsto g a f.small_sets ↔ ∀ t : set α, t ∈ f → ∀ᶠ k in a, g k ⊆ t :=
f.has_basis_small_sets.tendsto_right_iff


lemma tendsto_sup_dist {X Y : Type*} [topological_space X] [metric_space Y]
  {f : X → Y} {t : X} (h : continuous_at f t)
  {s : ℕ → set X} (hs : tendsto s at_top (𝓝 t).small_sets) :
  tendsto (λ (n : ℕ), ⨆ x ∈ s n, dist (f x) (f t)) at_top (𝓝 0) :=
begin
  rw metric.tendsto_nhds,
  have nonneg : ∀ n, 0 ≤ ⨆ x ∈ s n, dist (f x) (f t),
    from λ n, real.bcsupr_nonneg (λ _ _, dist_nonneg),
  simp only [dist_zero_right, real.norm_eq_abs, abs_of_nonneg, nonneg],
  intros ε ε_pos,
  apply ((𝓝 t).has_basis_small_sets.tendsto_right_iff.mp hs _ $
         metric.tendsto_nhds.mp h (ε/2) (half_pos ε_pos)).mono (λ n hn, _),
  apply lt_of_le_of_lt _ (half_lt_self ε_pos),
  exact real.bcsupr_le (half_pos ε_pos).le (λ x hx, (hn hx).out.le),
end
