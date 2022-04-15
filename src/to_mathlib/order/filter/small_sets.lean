import to_mathlib.data.real_basic
import to_mathlib.misc
import analysis.normed.group.basic

open_locale filter topological_space
open filter set metric

variables {α β ι : Type*}

namespace filter

/-- The filter `f.small_sets` is the largest filter containing all powersets of members of `f`. -/
def small_sets (f : filter α) : filter (set α) :=
⨅ t ∈ f, 𝓟 (𝒫 t)

lemma small_sets_eq_generate {f : filter α} : f.small_sets = generate (powerset '' f.sets) :=
by simp_rw [generate_eq_binfi, small_sets, infi_image, filter.mem_sets]

lemma has_basis_small_sets (f : filter α) :
  has_basis f.small_sets (λ t : set α, t ∈ f) powerset :=
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

lemma has_basis.small_sets {f : filter α} {p : ι → Prop} {s : ι → set α}
  (h : has_basis f p s) : has_basis f.small_sets p (λ i, 𝒫 (s i)) :=
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

lemma tendsto_small_sets_iff {la : filter α} {lb : filter β} {f : α → set β} :
  tendsto f la lb.small_sets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
(has_basis_small_sets lb).tendsto_right_iff

end filter
