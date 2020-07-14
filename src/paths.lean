import gluing
import analysis.convex.basic
/-!
# Continuous paths and path connectedness.
-/

noncomputable theory
open_locale classical topological_space filter
open filter set 

variables {X : Type*} [topological_space X]

local notation `I` := Icc (0 : ℝ) 1

lemma Icc_zero_one_refl {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

/-- A continuous path from `x` to `y` in `X` -/
structure path (x y : X):=
(to_fun : ℝ → X)
(cont' : continuous_on to_fun I)
(src' : to_fun 0 = x)
(tgt' : to_fun 1 = y)

variables {x y z : X}

instance : has_coe_to_fun (path x y):=
⟨_, path.to_fun⟩

-- Now restate fields of path in terms of the coercion

lemma path.cont (γ : path x y) : continuous_on γ I := γ.cont'

lemma path.src (γ : path x y) : γ 0 = x := γ.src'

lemma path.tgt (γ : path x y) : γ 1 = y := γ.tgt'

protected def path.const (x : X) : path x x :=
{ to_fun := λ t, x,
  cont' := continuous_const.continuous_on,
  src' := rfl,
  tgt' := rfl }

def path.symm (γ : path x y) : path y x :=
{ to_fun := λ t, γ (1 - t),
  cont' := begin
    intros t t_in,
    apply (γ.cont (1-t) (Icc_zero_one_refl.mp t_in)).comp,
    { exact continuous.continuous_within_at (continuous_const.sub continuous_id) },
    { intro t,
      rw [Icc_zero_one_refl],
      exact id, },
  end,
  src' :=  by simpa using γ.tgt',
  tgt' := by simpa using γ.src' }

def path.concat (f : path x y) (g : path y z) : path x z :=
{ to_fun := λ t, if t ≤ 1/2 then f (2*t) else g (2*t-1),
  cont' := begin
    apply continuous_on_if_Icc,
    { apply continuous_on.comp f.cont,
      { exact (continuous_const.mul continuous_id).continuous_on, },  
      { rintros x ⟨hx, hx'⟩,
        split ; dsimp only ; linarith } },
    { apply continuous_on.comp g.cont,
      { exact ((continuous_const.mul continuous_id).sub continuous_const).continuous_on, },  
      { rintros x ⟨hx, hx'⟩,
        split ; dsimp only ; linarith } },
    { norm_num,
      rw [f.tgt, g.src] },
  end,
  src' := by { convert f.src, norm_num },
  tgt' := by { convert g.tgt, norm_num } }

lemma path.concat_fst (f : path x y) (g : path y z) {t : ℝ} (h : t ≤ 1/2) : 
f.concat g t = f (2*t) :=
show (λ t, if t ≤ 1/2 then f (2*t) else  g (2*t-1)) t = _,
by simp_rw [if_pos h]

lemma path.concat_snd (f : path x y) (g : path y z) {t : ℝ} (h : ¬ t ≤ 1/2) : 
f.concat g t = g (2*t-1) :=
show (λ t, if t ≤ 1/2 then f (2*t) else  g (2*t-1)) t = _,
by simp_rw [not_lt, if_neg h]

lemma path.concat_snd' (f : path x y) (g : path y z) {t : ℝ} (h : t > 1/2) : 
f.concat g t = g (2*t-1) :=
show (λ t, if t ≤ 1/2 then f (2*t) else  g (2*t-1)) t = _,
by simp_rw [not_lt, if_neg (not_le_of_gt h)]

/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def joined_in (F : set X) : X → X → Prop :=
λ x y, ∃ γ : path x y, ∀ t ∈ I, γ t ∈ F

lemma joined_in.refl {x : X} {F : set X} (h : x ∈ F) : joined_in F x x :=
⟨path.const x, λ t t_in, h⟩

lemma joined_in.symm {x y} {F : set X} : joined_in F x y → joined_in F y x :=
begin
  rintros ⟨γ, h⟩,
  use γ.symm,
  intros t t_in,
  apply h,
  rwa Icc_zero_one_refl at t_in
end

lemma joined_in.trans {x y z : X} {F : set X} (hxy : joined_in F x y) (hyz : joined_in F y z) :
joined_in F x z :=
begin
  cases hxy with f hf,  
  cases hyz with g hg,
  use f.concat g,
  intros t t_in,
  rw mem_Icc at t_in,
  by_cases h : t ≤ 1/2,
  { rw path.concat_fst f g h,
    exact hf _ (by split ; linarith) },
  { rw path.concat_snd f g h,
    exact hg _ (by split ; linarith) }
end

lemma joined_in.mem {x y : X} {F : set X} (h : joined_in F x y) : x ∈ F ∧ y ∈ F :=
begin
  cases h with f hf,
  split ; [rw ← f.src, rw ← f.tgt] ; apply hf ; norm_num
end

variables (F : set X)

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def path_component (x : X) (F : set X) := {y | joined_in F x y}

/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def is_path_connected (F : set X) : Prop := ∃ x ∈ F, ∀ {y}, y ∈ F → joined_in F x y

lemma is_path_connected_iff_eq {F : set X} : is_path_connected F ↔  ∃ x ∈ F, path_component x F = F :=
begin
  split ; rintros ⟨x, x_in, h⟩ ; use [x, x_in],
  { ext y,
    exact ⟨λ hy, hy.mem.2, h⟩ },
  { intros y y_in,
    rwa ← h at y_in },
end

def joined_in_of_is_path_connected {F : set X} (h : is_path_connected F) :
  ∀ x y ∈ F, joined_in F x y :=
begin
  intros x y x_in y_in,
  rcases h with ⟨b, b_in, hb⟩,
  exact (hb x_in).symm.trans (hb y_in)
end

def is_path_connected_iff {F : set X} : is_path_connected F ↔ F.nonempty ∧ ∀ x y ∈ F, joined_in F x y :=
begin
  split,
  { exact λ h, ⟨by {rcases h with ⟨b, b_in, hb⟩, exact ⟨b, b_in⟩ }, joined_in_of_is_path_connected h⟩, },
  { rintros ⟨⟨b, b_in⟩, h⟩,
    exact ⟨b, b_in, λ x x_in, h b x b_in x_in⟩ },
end

-- attempts at some lemmas.

lemma zero_mem_I : (0 : ℝ) ∈ I := left_mem_Icc.2 zero_le_one
lemma one_mem_I : (1 : ℝ) ∈ I := right_mem_Icc.2 zero_le_one
lemma convex_I {t₁ t₂ s : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I) (hs : s ∈ I) :
  (1 - s) * t₁ + s * t₂ ∈ I :=
have h   : _, from convex_iff_segment_subset.mp (convex_Icc _ _) ht₁ ht₂,
have hs' : _, from Icc_zero_one_refl.mp hs,
  h ⟨_, _, hs'.1, hs.1, by linarith, rfl⟩

def path.image (γ : path x y) : set X := γ '' I

lemma path.image_src (γ : path x y) : x ∈ γ.image := ⟨0, zero_mem_I, γ.src⟩
lemma path.image_tgt (γ : path x y) : y ∈ γ.image := ⟨1,  one_mem_I, γ.tgt⟩

/-- the image of a path is connected. -/
lemma is_connected_path_image {γ : path x y} : is_connected γ.image :=
is_connected.image ⟨nonempty_Icc.2 zero_le_one, is_preconnected_Icc⟩ _ γ.2

/-- definition on a pair of points being joined in a set, in terms of the image of a path. -/
def joined_in_iff_path_image_subset {F : set X} : joined_in F x y ↔ ∃ γ : path x y, γ.image ⊆ F :=
iff.intro
  (λ ⟨γ, hγ⟩, ⟨γ, λ y ⟨t, ht, hy⟩, hy ▸ (hγ t ht)⟩)
  (λ ⟨γ, hγ⟩, ⟨γ, λ t ht, hγ ⟨t, ht, rfl⟩⟩)

/-- a path connected set is connected.-/
lemma is_connected_of_is_path_connected {F : set X} (h : is_path_connected F) : is_connected F :=
let ⟨x, hx, hj⟩ := h in ⟨⟨x, hx⟩, is_preconnected_of_forall x (λ y hy,
let ⟨γ, hγ⟩ := joined_in_iff_path_image_subset.1 (hj hy) in
  ⟨γ.image, hγ, γ.image_src, γ.image_tgt, is_connected_path_image.2⟩)⟩

/-- truncation of a path. -/
def path.trunc (γ : path x y) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I) : path (γ t₁) (γ t₂) :=
{ to_fun := λ t, γ ((1 - t) * t₁ + t * t₂),
  cont'  := begin
apply continuous_on.comp,
{ exact γ.cont' },
{ exact continuous_on.add
    (continuous_on.mul (continuous_on.sub continuous_on_const continuous_on_id) continuous_on_const)
    (continuous_on.mul continuous_on_id continuous_on_const) },
{ intros s hs, apply mem_preimage.mpr, exact convex_I ht₁ ht₂ hs }
end,
  src'   := congr_arg _ (by linarith),
  tgt'   := congr_arg _ (by linarith),
}

-- in hingsight, maybe path.trunc should more preferably be 'stay at x
-- until t₁ then stay at y after t₂' rather than what is defined here,

lemma path.trunc_interval (γ : path x y) {t₁ t₂ t : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I)
  (ht : t ∈ I) : γ.trunc ht₁ ht₂ t = γ ((1 - t) * t₁ + t * t₂) := rfl

def path.trunc_left (γ : path x y) {t : ℝ} (ht : t ∈ I) : path x (γ t) :=
let γ' := γ.trunc zero_mem_I ht in
  ⟨γ', γ'.cont', by { rw γ.trunc_interval _ _ zero_mem_I, simp [γ.src] }, γ'.tgt⟩

def path.trunc_right (γ : path x y) {t : ℝ} (ht : t ∈ I) : path (γ t) y :=
let γ' := γ.trunc ht one_mem_I in
  ⟨γ', γ'.cont, γ'.src, by { rw γ.trunc_interval _ _ one_mem_I, simp [γ.tgt] }⟩

lemma path.trunc_image (γ : path x y) {t₁ t₂ t : ℝ} {ht₁ : t₁ ∈ I} {ht₂ : t₂ ∈ I} :
  (γ.trunc ht₁ ht₂).image ⊆ γ.image :=
λ x ⟨t, ht, hx⟩, ⟨_, convex_I ht₁ ht₂ ht, by rwa ←γ.trunc_interval ht₁ ht₂ ht⟩

lemma path.trunc_left_image (γ : path x y) {t : ℝ} {ht : t ∈ I} : (γ.trunc_left ht).image ⊆ γ.image :=
λ x ⟨s, hs, hx⟩, ⟨_, convex_I zero_mem_I ht hs, by rwa ←γ.trunc_interval zero_mem_I ht hs⟩

lemma path.trunc_right_image (γ : path x y) {t : ℝ} {ht : t ∈ I} : (γ.trunc_right ht).image ⊆ γ.image :=
λ x ⟨s, hs, hx⟩, ⟨_, convex_I ht one_mem_I hs, by rwa ←γ.trunc_interval ht one_mem_I hs⟩

-- also in hindsight: maybe truncation should just be done in terms of
-- images?  the following operations come up frequently enough that I
-- feel the need for an easy way to get to them, but I suspect there's
-- a more straightforward way than explicitly defining the following:

def path.replace_endpoints (γ : path x y) {x' y' : X} (hx : x = x') (hy : y = y') : path x' y' :=
⟨γ, γ.cont, hx ▸ γ.src, hy ▸ γ.tgt⟩

def path.replace_src (γ : path x y) {x' : X} (hx : x = x') : path x' y := γ.replace_endpoints hx rfl
def path.replace_tgt (γ : path x y) {y' : X} (hy : y = y') : path x y' := γ.replace_endpoints rfl hy

/-- the image of a path is path connected. -/
lemma is_path_connected_path_image {γ: path x y} : is_path_connected γ.image :=
⟨x, γ.image_src, λ w ⟨t, ht, hw⟩,
  joined_in_iff_path_image_subset.mpr ⟨(γ.trunc_left ht).replace_tgt hw, by { apply γ.trunc_left_image, assumption }⟩⟩

lemma joined_in.mono {F G : set X} (h : G ⊆ F) : joined_in G x y → joined_in F x y :=
λ ⟨γ, hγ⟩, ⟨γ, λ t ht, h (hγ t ht)⟩

lemma path_component_subset {F : set X} : path_component x F ⊆ F :=
λ y ⟨γ, hγ⟩, γ.tgt ▸ (hγ _ (right_mem_Icc.2 zero_le_one))

lemma subset_path_component {F G : set X} (hG : G ⊆ F) (h : is_path_connected G) (hx : x ∈ G) : G ⊆ path_component x F :=
λ y hy, joined_in.mono hG (joined_in_of_is_path_connected h _ _ hx hy)

lemma path_component_idem {F : set X} : path_component x (path_component x F) = path_component x F :=
subset.antisymm
  path_component_subset
  (λ y ⟨γ, hγ⟩, joined_in_iff_path_image_subset.mpr
    ⟨γ, subset_path_component (λ w ⟨t, ht, hw⟩, hw ▸ hγ t ht) is_path_connected_path_image γ.image_src⟩)

lemma is_path_connected_path_component {F : set X} (hx : x ∈ F): is_path_connected (path_component x F) :=
⟨x, joined_in.refl hx, λ y hy, show y ∈ path_component x _, by rwa path_component_idem⟩

lemma path_components_eq {F : set X} (h : joined_in F x y) : path_component x F = path_component y F :=
subset.antisymm (λ z hz, h.symm.trans hz) (λ z hz, h.trans hz)

section locally_path_connected

/-- a top. space is locally path connected if it has a neighbourhood base of connected sets. -/
class locally_path_connected_space (α : Type*) [topological_space α] :=
(local_path_connected_nhds : ∀ (x : α) (n ∈ 𝓝 x), ∃ (u ∈ 𝓝 x), u ⊆ n ∧ is_path_connected u)

-- in an experiement in adhering to the don't-descend-into-subtypes
-- theme, we define the following, modelled after is_preconnected /
-- is_preconnected_space in mathlib:

variables {α : Type*} [topological_space α] {a : α}

def is_locally_path_connected (s : set α) : Prop :=
∀ (x ∈ s) (n ∈ nhds_within x s), ∃ (u ∈ nhds_within x s), u ⊆ n ∧ is_path_connected u

-- the big awful brittle blob two lemmas down is analogous to
-- is_open_iff_mem_nhds in the subtype. it's written down like that
-- because I was eager to move on to the more immediately relevant
-- results, but if we expect to develop a body of lemmas about
-- relatively open sets, this bears refactoring.

/-- u is (relatively) open within s if it is open in s with the subspace topology. -/
def is_open_within (s u : set α) : Prop := ∃ v, is_open v ∧ u = v ∩ s

lemma is_open_within_univ {u : set α} : is_open_within univ u ↔ is_open u :=
⟨λ ⟨v, hvo, huv⟩, huv.symm ▸ is_open_inter hvo is_open_univ, λ huo, ⟨u, huo, (inter_univ _).symm⟩⟩

lemma is_open_within_iff_mem_nhds_within {s u : set α} :
  is_open_within s u ↔ u ⊆ s ∧ ∀ a ∈ u, u ∈ nhds_within a s :=
iff.intro
(λ ⟨_, hvo, hvi⟩, and.intro
  (hvi.symm ▸ inter_subset_right _ s)
  (λ a ha, mem_nhds_within.mpr ⟨_, hvo, by { rw hvi at ha, exact ha.left }, by rw hvi⟩))
(λ ⟨hu, h⟩, exists.intro (⋃₀ {v : set α | is_open v ∧ v ∩ s ⊆ u })
(and.intro
  (is_open_sUnion (λ _ ⟨ht, _⟩, ht))
  (subset.antisymm
    (λ _ ha,
      let ⟨_, hvo, hav, hvi⟩ := mem_nhds_within.1 (h _ ha) in
      mem_inter
        (mem_sUnion.2 ⟨_, ⟨hvo, hvi⟩, hav⟩) (hu ha))
    (λ _ ⟨hxu, hxs⟩, let ⟨_, ⟨_, hwi⟩, hxw⟩ := mem_sUnion.2 hxu in
      hwi ⟨hxw, hxs⟩))))

-- likewise; this is analogous to is_open_bUnion.

lemma is_open_within_bUnion {s : set α} {β : Type*} {J : set β} {f : β → set α}
  (h : ∀ i ∈ J, is_open_within s (f i)) : is_open_within s ⋃ i ∈ J, f i :=
sorry

lemma path_component_mem_nhds_within {s : set α} (h : is_locally_path_connected s) (ha : a ∈ s) :
  path_component a s ∈ nhds_within a s :=
let ⟨_, hun, hus, hup⟩ := h _ ha _ self_mem_nhds_within in
let ⟨_, hvo, hav, hvs⟩ := mem_nhds_within.mp hun in
  (nhds_within a s).sets_of_superset hun (subset_path_component hus hup (hvs (mem_inter hav ha)))

lemma is_open_within_path_component {s : set α} (h : is_locally_path_connected s) (ha : a ∈ s) :
  is_open_within s (path_component a s) :=
let ⟨u, hun, hus, hup⟩ := h _ ha _ self_mem_nhds_within in
  is_open_within_iff_mem_nhds_within.mpr ⟨path_component_subset, λ b hb,
    path_components_eq hb.symm ▸ path_component_mem_nhds_within h (path_component_subset hb)⟩

-- ... and the analogous statements for a locally_path_connected_space
-- are retried by replacing s with the appropriate univ:

variable [locally_path_connected_space α]

/-- opens sets in a locally path connected space is locally path connected. -/
lemma is_locally_path_connected_of_open {s : set α} (hs : is_open s) : is_locally_path_connected s :=
λ x hx n hn, let ⟨u, hu, hun, hup⟩ := locally_path_connected_space.local_path_connected_nhds x n
                                      (nhds_of_nhds_within_of_nhds (mem_nhds_sets hs hx) hn) in
let ⟨t, htu, hto, hxt⟩ := mem_nhds_sets_iff.mp hu in
  ⟨u, mem_nhds_within.mpr ⟨t, hto, hxt, subset.trans (inter_subset_left _ _) htu⟩, hun, hup⟩

lemma is_locally_path_connected_univ : is_locally_path_connected (univ : set α) :=
is_locally_path_connected_of_open (is_open_univ)

lemma path_component_mem_nhds : path_component a univ ∈ nhds a :=
by { rw ←nhds_within_univ, exact path_component_mem_nhds_within is_locally_path_connected_univ (mem_univ _)}

-- the next proof is very verbose

/-- path components of a locally connected space are open. -/
lemma is_open_path_component : is_open (path_component a univ) :=
by { rw ←is_open_within_univ, exact is_open_within_path_component is_locally_path_connected_univ (mem_univ _)}

lemma is_path_connected_iff_is_connected {s : set α} (hs : is_open s) : is_path_connected s ↔ is_connected s :=
iff.intro
  (λ hp, is_connected_of_is_path_connected hp)
  (λ hc,
let ⟨a, ha⟩ := hc.1 in
let h := is_preconnected_iff_subset_of_disjoint.mp hc.2 in
begin
  by_contradiction a₁, suffices h : ¬ is_preconnected s, exact h hc.2,

  have hp, from is_locally_path_connected_of_open hs, -- s is locally path connected.

  -- u = U ∩ s is the path component of a, relatively open in s.
  let u := path_component a s,
  have huo : is_open_within s u, from
    is_open_within_path_component hp ha,
  rcases huo with ⟨U, hUo, hUi⟩,

  have hupc : is_path_connected u, from is_path_connected_path_component ha,

  --have hus : u ⊆ s, from path_component_subset,

  -- v = V ∩ s is the union of all the other path components, likewise
  -- relatively open in s.
  let v := ⋃ (b ∈ s \ u), (path_component b s),
  have hvo : is_open_within s v, from
    is_open_within_bUnion (λ b ⟨hbs, hhbu⟩, is_open_within_path_component hp hbs),
  rcases hvo with ⟨V, hVo, hVi⟩,

  -- u and v together cover s :
  have huvc : s ⊆ u ∪ v, from λ x hxs, classical.by_cases
    (λ hxu : x ∈ u, or.intro_left _ hxu)
    (λ hxn, or.intro_right _ (mem_bUnion_iff.2 ⟨x, ⟨hxs, hxn⟩, joined_in.refl hxs⟩)),

  -- (a different formulation that is useful elsewhere: i am not very
  -- good at wrangling sets.)
  have huvc₂ : ∀ x ∈ s, x ∉ u → x ∈ v, from λ x hxs hxu, or.elim
    ((mem_union _ _ _).1 (huvc hxs)) (λ hxu', absurd hxu' hxu) id,

  -- none of the other path components intersect u ...
  have hvi: ∀ (b ∈ s \ u) (x ∈ u), x ∉ path_component b s , from
    λ m ⟨hms, hmu⟩ x hxu hjmx, hmu (hxu.trans hjmx.symm),

  -- ... so their union is disoint from u.
  have huve : u ∩ v = ∅, from
    eq_empty_iff_forall_not_mem.mpr (λ _ ⟨hxu, hxv⟩,
    let ⟨_, hb, hjbx⟩ := mem_bUnion_iff.1 hxv in hvi _ hb _ hxu hjbx),

  have huU : u ⊆ U, from hUi.symm ▸ inter_subset_left _ _,
  have hvV : v ⊆ V, from hVi.symm ▸ inter_subset_left _ _,

  have hUVc: s ⊆ U ∪ V, from subset.trans huvc (union_subset_union huU hvV),

  have hUne : (s ∩ U).nonempty, from nonempty_of_mem ⟨ha, huU $ joined_in.refl ha⟩,

  -- why the frick is this the hardest part of the proof?
  have : ∃ b, b ∈ s \ u, from sorry,
  rcases this with ⟨b, hbs, hbu⟩,

  have hVne : (s ∩ V).nonempty, from nonempty_of_mem ⟨hbs, hvV (huvc₂ _ hbs hbu)⟩,

  have huvUV : u ∩ v = s ∩ (U ∩ V), by rw [hUi, hVi, inter_comm V s, inter_assoc, ←inter_assoc s,
                                           inter_self, inter_comm, inter_assoc, inter_comm U],

  -- assuming preconnectedness, arrive at contradiction.
  have hUVe : (s ∩ (U ∩ V)) = ∅, from huvUV ▸ huve,
  intro hsc,
  have hUVne : (s ∩ (U ∩ V)).nonempty, from hsc _ _ hUo hVo hUVc hUne hVne,

  exact not_nonempty_iff_eq_empty.2 hUVe hUVne,
end)

end locally_path_connected
