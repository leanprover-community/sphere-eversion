import topology.instances.real

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

instance : has_zero I := ⟨⟨0, by split ; norm_num⟩⟩

instance : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

def proj_I : ℝ → I :=
λ t, if h : t ≤ 0 then ⟨0, left_mem_Icc.mpr zero_le_one⟩ else 
     if h' : t ≤ 1 then ⟨t, ⟨le_of_lt $ not_le.mp h, h'⟩⟩ else ⟨1, right_mem_Icc.mpr zero_le_one⟩

lemma proj_I_I {t : ℝ} (h : t ∈ I) : proj_I t = ⟨t, h⟩ :=
begin
  unfold proj_I,
  rw mem_Icc at h,
  split_ifs,
  { simp [show t = 0, by linarith] },
  { refl },
  { exfalso, linarith }
end

lemma range_proj_I : range proj_I = univ :=
begin
  rw eq_univ_iff_forall,
  rintro ⟨t, t_in⟩,
  use [t, proj_I_I t_in],
end

lemma Iic_def (x : ℝ) : {t | t ≤ x} = Iic x := rfl

local attribute [simp] Iic_def

lemma continuous_proj_I : continuous proj_I :=
begin
  refine continuous_induced_rng' (coe : I → ℝ) rfl _,
  have : continuous (λ t : ℝ, if t ≤ 0 then 0 else if t ≤ 1 then t else 1),
  by refine continuous_if _ continuous_const (continuous_if _ continuous_id continuous_const) ; simp [zero_le_one],
  convert this,
  ext,
  dsimp [proj_I],
  split_ifs ; refl
end

def I_extend {β : Type*} (f : I → β) : ℝ → β :=
f ∘ proj_I

lemma continuous.I_extend {f : I → X} (hf : continuous f) : continuous (I_extend f) :=
hf.comp continuous_proj_I 

lemma I_extend_extends (f : I → X) {t : ℝ} (ht : t ∈ I) : I_extend f t = f ⟨t, ht⟩ :=
by simp [I_extend, proj_I_I, ht]

lemma I_extend_zero (f : I → X) : I_extend f 0 = f 0 :=
I_extend_extends _ _

lemma I_extend_one (f : I → X) : I_extend f 1 = f 1 :=
I_extend_extends _ _

@[simp] lemma I_extend_range (f : I → X) : range (I_extend f) = range f :=
begin
  rw [I_extend, range_comp],
  convert image_univ,
  exact range_proj_I
end

instance : connected_space I := subtype.connected_space ⟨⟨0, by split ; norm_num⟩, is_preconnected_Icc⟩

/-- A continuous path from `x` to `y` in `X` -/
structure path (x y : X):=
(to_fun : ℝ → X)
(cont' : continuous to_fun)
(src' : to_fun 0 = x)
(tgt' : to_fun 1 = y)

variables {x y z : X}

instance : has_coe_to_fun (path x y):=
⟨_, path.to_fun⟩

-- Now restate fields of path in terms of the coercion

lemma path.cont (γ : path x y) : continuous γ := γ.cont'

lemma path.src (γ : path x y) : γ 0 = x := γ.src'

lemma path.tgt (γ : path x y) : γ 1 = y := γ.tgt'

protected def path.const (x : X) : path x x :=
{ to_fun := λ t, x,
  cont' := continuous_const,
  src' := rfl,
  tgt' := rfl }

def path.symm (γ : path x y) : path y x :=
{ to_fun := λ t, γ (1 - t),
  cont' := γ.cont.comp (continuous_const.sub continuous_id),
  src' :=  by simpa using γ.tgt',
  tgt' := by simpa using γ.src' }

lemma path.symm_mem {γ : path x y} {F : set X} (h : ∀ t ∈ I, γ t ∈ F) : ∀ t ∈ I, γ.symm t ∈ F :=
λ t t_in, h _ (Icc_zero_one_refl.mp t_in)

def path.concat (f : path x y) (g : path y z) : path x z :=
{ to_fun := λ t, if t ≤ 1/2 then f (2*t) else g (2*t-1),
  cont' := continuous_if  (by norm_num [f.tgt, g.src]) 
                          (f.cont.comp (continuous_const.mul continuous_id))
                          (g.cont.comp ((continuous_const.mul continuous_id).sub continuous_const)),
  src' := by { convert f.src, norm_num },
  tgt' := by { convert g.tgt, norm_num } }

lemma path.concat_fst (f : path x y) (g : path y z) {t : ℝ} (h : t ≤ 1/2) : 
  f.concat g t = f (2*t) :=
show (λ t, if t ≤ 1/2 then f (2*t) else  g (2*t-1)) t = _,
by simp_rw [if_pos h]

lemma path.concat_snd (f : path x y) (g : path y z) {t : ℝ} (h : ¬ t ≤ 1/2) : 
  f.concat g t = g (2*t-1) :=
show ite _ _ _ = _, by simp_rw [if_neg h]

lemma path.concat_snd' (f : path x y) (g : path y z) {t : ℝ} (h : t > 1/2) : 
  f.concat g t = g (2*t-1) :=
show ite _ _ _ = _, by simp_rw [if_neg (not_le_of_gt h)]

lemma path.concat_mem {f : path x y} {g : path y z} {F G : set X} (hf : ∀ t ∈ I, f t ∈ F) (hg : ∀ t ∈ I, g t ∈ G) :
  ∀ t ∈ I, f.concat g t ∈ F ∪ G:=
begin
  intros t t_in,
  cases le_or_gt t (1/2) with h h,
  { left,
    rw path.concat_fst _ _ h, 
    apply hf, 
    rw mem_Icc at *,
    split ; linarith },
  { right,
    rw path.concat_snd' _ _ h,
    apply hg, 
    rw mem_Icc at *,
    split ; linarith },
end

lemma path.concat_mem_same {f : path x y} {g : path y z} {F : set X} (hf : ∀ t ∈ I, f t ∈ F) (hg : ∀ t ∈ I, g t ∈ F) :
  ∀ t ∈ I, f.concat g t ∈ F :=
by simpa only [union_self] using path.concat_mem hf hg

/-- The relation "being joined by a path". This is an equivalence relation. -/
def joined (x y : X) : Prop := ∃ γ : I → X, continuous γ ∧ γ 0 = x ∧ γ 1 = y

/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def joined_in (F : set X) (x y : X) : Prop :=
∃ γ : I → X, continuous γ ∧ (∀ t, γ t ∈ F) ∧ γ 0 = x ∧ γ 1 = y

lemma joined_in.joined {x y : X} {F : set X} : joined_in F x y → joined x y 
| ⟨γ, γ_cont, γ_in, γ_src, γ_tgt⟩ := ⟨γ, γ_cont, γ_src, γ_tgt⟩

@[simp] lemma joined_in_univ {x y : X} : joined_in univ x y ↔ joined x y :=
by simp [joined_in, joined]

def joined_in.path {F : set X} {x y : X} (h : joined_in F x y) : path x y :=
{ to_fun := I_extend (classical.some h),
  cont' := (classical.some_spec h).1.I_extend,
  src' := by simpa only [I_extend_zero] using (classical.some_spec h).2.2.1,
  tgt' := by simpa only [I_extend_one] using (classical.some_spec h).2.2.2 }

lemma joined_in.path_mem' {F : set X} {x y : X} (h : joined_in F x y) : ∀ t, h.path t ∈ F :=
begin
  suffices : range h.path ⊆ F, by rwa ← range_subset_iff,
  erw [I_extend_range, range_subset_iff],
  exact (classical.some_spec h).2.1
end

lemma joined_in.path_mem {F : set X} {x y : X} (h : joined_in F x y) : ∀ t ∈ I, h.path t ∈ F :=
λ t t_in, h.path_mem' t

def path.joined_in {F : set X} {x y : X} (γ : path x y) (h : ∀ t ∈ I, γ t ∈ F) : joined_in F x y :=
⟨γ ∘ coe, γ.cont.comp continuous_subtype_coe, λ ⟨t, t_in⟩, h t t_in, γ.src, γ.tgt⟩

lemma joined_in.refl {x : X} {F : set X} (h : x ∈ F) : joined_in F x x :=
⟨λ t, x, continuous_const, λ t, h, rfl, rfl⟩

lemma joined_in.symm {x y} {F : set X} (h : joined_in F x y) : joined_in F y x :=
h.path.symm.joined_in (path.symm_mem h.path_mem)

lemma joined_in.trans {x y z : X} {F : set X} (hxy : joined_in F x y) (hyz : joined_in F y z) :
  joined_in F x z :=
(hxy.path.concat hyz.path).joined_in (path.concat_mem_same hxy.path_mem hyz.path_mem)

lemma joined.refl (x : X) : joined x x :=
by { rw ← joined_in_univ, exact joined_in.refl trivial }
  
lemma joined.symm {x y : X} (h : joined x y) : joined y x :=
by { rw ← joined_in_univ at *, exact joined_in.symm h }

lemma joined.trans {x y z : X} (hxy : joined x y) (hyz : joined y z) :
  joined x z :=
by { rw ← joined_in_univ at *, exact joined_in.trans hxy hyz }

lemma joined_in.mem {x y : X} {F : set X} (h : joined_in F x y) : x ∈ F ∧ y ∈ F :=
begin
  rcases h with ⟨γ, γ_cont, γ_in, γ_src, γ_tgt⟩,
  split ; [rw ← γ_src, rw ← γ_tgt] ; apply γ_in ; norm_num
end

lemma joined_in.mono {U V : set X} {x y : X} (h : joined_in U x y) (hUV : U ⊆ V) : joined_in V x y :=
let ⟨f, f_cont, f_in, f_src, f_tgt⟩ := h in ⟨f, f_cont, λ t, hUV (f_in t), f_src, f_tgt⟩

def joined_in.map {x y : X} {F : set X} (h : joined_in F x y) : I → F :=
λ t, ⟨h.path t, h.path_mem t t.property⟩

def joined_in.continuous_map {x y : X} {F : set X} (h : joined_in F x y) : continuous h.map :=
continuous_subtype_mk _ (h.path.cont.comp continuous_subtype_coe)

lemma joined_in.map_zero {x y : X} {F : set X} (h : joined_in F x y) : h.map 0 = ⟨x, h.mem.1⟩ :=
subtype.ext h.path.src

lemma joined_in.map_one {x y : X} {F : set X} (h : joined_in F x y) : h.map 1 = ⟨y, h.mem.2⟩ :=
subtype.ext h.path.tgt

variables (F : set X)

/-- The path component of `x` is the set of points that can be joined to `x`. -/
def path_component (x : X) := {y | joined x y}

@[simp] lemma mem_path_component_self (x : X) : x ∈ path_component x :=
joined.refl x

@[simp] lemma path_component.nonempty (x : X) : (path_component x).nonempty := 
⟨x, mem_path_component_self x⟩

lemma path_of_mem {x y : X} (h : y ∈ path_component x) : path x y :=
{ to_fun := I_extend (classical.some h),
  cont' := (classical.some_spec h).1.I_extend,
  src' := by simpa only [I_extend_zero] using (classical.some_spec h).2.1,
  tgt' := by simpa only [I_extend_one] using (classical.some_spec h).2.2 }

lemma mem_path_component_of_mem {x y : X} (h : x ∈ path_component y) : y ∈ path_component x :=
joined.symm h

lemma path_component_symm {x y : X} : x ∈ path_component y ↔ y ∈ path_component x :=
⟨λ h, mem_path_component_of_mem h, λ h, mem_path_component_of_mem h⟩

lemma path_component_congr {x y : X} (h : x ∈ path_component y) : path_component x = path_component y:=
begin
  ext z,
  split,
  { intro h',
    rw path_component_symm,
    exact (h.trans h').symm },
  { intro h',
    rw path_component_symm at h' ⊢,
    exact h'.trans h },
end

lemma path_component_subset_component (x : X) : path_component x ⊆ connected_component x :=
λ y ⟨f, f_cont, f_src, f_tgt⟩, subset_connected_component (is_connected_range f_cont).2 ⟨0, f_src⟩ ⟨1, f_tgt⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def path_component_in (x : X) (F : set X) := {y | joined_in F x y}

@[simp] lemma path_component_in_univ (x : X) : path_component_in x univ = path_component x :=
by simp [path_component_in, path_component, joined_in, joined]

lemma joined.mem_path_component {x y z : X} (hyz : joined y z) (hxy : y ∈ path_component x) : z ∈ path_component x :=
hxy.trans hyz


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def is_path_connected (F : set X) : Prop := ∃ x ∈ F, ∀ {y}, y ∈ F → joined_in F x y

lemma is_path_connected_iff_eq {F : set X} : is_path_connected F ↔  ∃ x ∈ F, path_component_in x F = F :=
begin
  split ; rintros ⟨x, x_in, h⟩ ; use [x, x_in],
  { ext y,
    exact ⟨λ hy, hy.mem.2, h⟩ },
  { intros y y_in,
    rwa ← h at y_in },
end

lemma is_path_connected.joined_in {F : set X} (h : is_path_connected F) :
  ∀ x y ∈ F, joined_in F x y :=
λ x y x_in y_in, let ⟨b, b_in, hb⟩ := h in (hb x_in).symm.trans (hb y_in)

def is_path_connected.path {x y : X} {F : set X} (h : is_path_connected F) (x_in : x ∈ F) (y_in : y ∈ F) : path x y :=
(h.joined_in x y x_in y_in).path

def is_path_connected.path_mem {x y : X} {F : set X} (h : is_path_connected F) (x_in : x ∈ F) (y_in : y ∈ F) : 
  ∀ t ∈ I, h.path x_in y_in t ∈ F :=
joined_in.path_mem _

lemma is_path_connected_iff {F : set X} : is_path_connected F ↔ F.nonempty ∧ ∀ x y ∈ F, joined_in F x y :=
⟨λ h, ⟨let ⟨b, b_in, hb⟩ := h in ⟨b, b_in⟩, h.joined_in⟩, 
 λ ⟨⟨b, b_in⟩, h⟩, ⟨b, b_in, λ x x_in, h b x b_in x_in⟩⟩

lemma is_path_connected.image {Y : Type*} [topological_space Y] {F : set X} (hF : is_path_connected F) {f : X → Y} (hf : continuous f) : 
  is_path_connected (f '' F) :=
begin
  rcases hF with ⟨x, x_in, hx⟩,
  use [f x, mem_image_of_mem f x_in],
  rintros _ ⟨y, y_in, rfl⟩,
  rcases hx y_in with ⟨γ, γ_cont, γ_in, rfl, rfl⟩,
  use [f ∘ γ, hf.comp γ_cont, λ t, ⟨γ t, γ_in t, rfl⟩, rfl, rfl]
end

lemma is_path_connected.mem_path_component {x y : X} {s : set X} (hs : is_path_connected s) (x_in : x ∈ s) (y_in : y ∈ s) :
  y ∈ path_component x :=
(hs.joined_in x y x_in y_in).joined

lemma  is_path_connected.subset_path_component {x : X} {s : set X} (hs : is_path_connected s) (x_in : x ∈ s) :
  s ⊆ path_component x :=
λ y y_in, hs.mem_path_component x_in y_in


lemma is_path_connected.union {U V : set X} (hU : is_path_connected U) (hV : is_path_connected V) 
  (hUV : (U ∩ V).nonempty) : is_path_connected (U ∪ V) :=
begin
  rcases hUV with ⟨x, xU, xV⟩,
  use [x, or.inl xU],
  rintros y (yU | yV),
  { exact (hU.joined_in x y xU yU).mono (subset_union_left U V) },
  { exact (hV.joined_in x y xV yV).mono (subset_union_right U V) },
end

lemma is_path_connected.preimage_coe {U W : set X} (hW : is_path_connected W) (hWU : W ⊆ U) : is_path_connected ((coe : U → X) ⁻¹' W) :=
begin
  rcases hW with ⟨x, x_in, hx⟩,
  use [⟨x, hWU x_in⟩, by simp [x_in]],
  rintros ⟨y, hyU⟩ hyW,
  change y ∈ W at hyW,
  rcases hx hyW with ⟨γ, γ_cont, γ_mem, rfl, rfl⟩,
  exact ⟨λ t, ⟨γ t, hWU $ γ_mem t⟩, continuous_subtype_mk _ γ_cont, γ_mem, rfl, rfl⟩,
end


class path_connected_space (X : Type*) [topological_space X] : Prop :=
(nonempty : nonempty X)
(ex_path : ∀ x y : X, joined x y)

attribute [instance, priority 500] path_connected_space.nonempty

namespace path_connected_space 
variables [topological_space X] [path_connected_space X]

def path (x y : X) : path x y := 
{ to_fun := I_extend (classical.some (ex_path x y)),
  cont' := (classical.some_spec $ ex_path x y).1.I_extend,
  src' := by simp [(classical.some_spec $ ex_path x y).2.1, I_extend_zero],
  tgt' := by simp [(classical.some_spec $ ex_path x y).2.2, I_extend_one] }

end path_connected_space

lemma is_path_connected_iff_path_connected_space {F : set X} : is_path_connected F ↔ path_connected_space F :=
begin
  rw is_path_connected_iff,
  split,
  { rintro ⟨⟨x, x_in⟩, h⟩,
    refine ⟨⟨⟨x, x_in⟩⟩, _⟩,
    rintros ⟨y, y_in⟩ ⟨z, z_in⟩,
    let H := h y z y_in z_in,
    use [H.map, H.continuous_map, H.map_zero, H.map_one] },
  { rintros ⟨⟨x, x_in⟩, H⟩,
    refine ⟨⟨x, x_in⟩, λ y z y_in z_in, _⟩,
    rcases H ⟨y, y_in⟩ ⟨z, z_in⟩ with ⟨f, f_cont, f_src, f_tgt⟩,
    use [coe ∘ f, by continuity!],
    simp [*] }
end

lemma path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X) :=
begin
  split,
  { introI h,
    inhabit X,
    refine ⟨default X, mem_univ _, _⟩,
    simpa [joined_in] using  path_connected_space.ex_path (default X) },
  { intro h,
    have h' := h.joined_in,
    cases h with x h,
    exact ⟨⟨x⟩, by simpa using h'⟩ },
end

lemma path_connected_space_iff_eq : path_connected_space X ↔ ∃ x : X, path_component x = univ :=
by simp [path_connected_space_iff_univ, is_path_connected_iff_eq]

instance path_connected_space.connected_space [path_connected_space X] : connected_space X :=
begin
  rw connected_space_iff_connected_component,
  rcases is_path_connected_iff_eq.mp (path_connected_space_iff_univ.mp ‹_›) with ⟨x, x_in, hx⟩,
  use x,
  rw ← univ_subset_iff,
  exact (by simpa using hx : path_component x = univ) ▸ path_component_subset_component x
end

class loc_path_connected_space (X : Type*) [topological_space X] :=
(path_connected_basis : ∀ x : X, (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s) id)

export loc_path_connected_space (path_connected_basis)

lemma path_connected_space_iff_connected_space [loc_path_connected_space X] : 
  path_connected_space X ↔ connected_space X :=
begin
  split,
  { introI h,
    apply_instance },
  { introI hX,
    inhabit X,
    let x₀ := default X,
    rw path_connected_space_iff_eq,
    use x₀,
    refine eq_univ_of_nonempty_clopen (by simp) ⟨_, _⟩, 
    { rw is_open_iff_mem_nhds,
      intros y y_in,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      apply mem_sets_of_superset U_in,
      rw ← path_component_congr y_in,
      exact hU.subset_path_component (mem_of_nhds U_in) },
    { rw is_closed_iff_nhds,
      intros y H,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      rcases H U U_in with ⟨z, hz, hz'⟩,
      exact ((hU.joined_in z y hz $ mem_of_nhds U_in).joined.mem_path_component hz') } },
end

-- The next two lemmas should move close to subtype.preconnected_space 
lemma is_preconnected_iff_preconnected_space {s : set X} : is_preconnected s ↔ preconnected_space s :=
begin
  refine ⟨subtype.preconnected_space, _⟩,
  rintros ⟨h⟩,
  intros U V U_op V_op hsUV hsU hsV,
  specialize h (coe ⁻¹' U) (coe ⁻¹' V) (continuous_subtype_coe U U_op) (continuous_subtype_coe V V_op) _ _ _,
  { rw ← subtype.preimage_coe_nonempty,
    simpa using h },
  { rwa [← preimage_union, ← image_subset_iff, subtype.coe_image_univ s] },
  { simpa [subtype.preimage_coe_nonempty] using hsU },
  { simpa [subtype.preimage_coe_nonempty] using hsV }
end

lemma is_connected_iff_connected_space {s : set X} : is_connected s ↔ connected_space s :=
⟨subtype.connected_space, λ h, ⟨nonempty_subtype.mp h.2, is_preconnected_iff_preconnected_space.mpr h.1⟩⟩

lemma path_connected_subset_basis [loc_path_connected_space X] {U : set X} (h : is_open U) 
  {x : X} (hx : x ∈ U) : (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s ∧ s ⊆ U) id :=
(path_connected_basis x).has_basis_self_subset (mem_nhds_sets h hx)

lemma loc_path_connected_of_is_open [loc_path_connected_space X] {U : set X} (h : is_open U) :
  loc_path_connected_space U :=
⟨begin
  rintros ⟨x, x_in⟩,
  rw nhds_subtype_eq_comap,
  constructor,
  intros V,
  rw (has_basis.comap (coe : U → X) (path_connected_subset_basis h x_in)).mem_iff,
  split,
  { rintros ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩,
    exact ⟨coe ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩ },
  { rintros ⟨W, ⟨W_in, hW⟩, hWV⟩,
    refine ⟨coe '' W, ⟨filter.image_coe_mem_sets (mem_nhds_sets h x_in) W_in,
                       hW.image continuous_subtype_coe, subtype.coe_image_subset U W⟩, _⟩,
    rintros x ⟨y, ⟨y_in, hy⟩⟩,
    rw ← subtype.coe_injective hy,
    tauto },
end⟩

lemma is_open.is_connected_iff_is_path_connected [loc_path_connected_space X] {U : set X} (U_op : is_open U) :
 is_path_connected  U ↔ is_connected U :=
begin
  rw [is_connected_iff_connected_space, is_path_connected_iff_path_connected_space],
  haveI := loc_path_connected_of_is_open U_op,
  exact path_connected_space_iff_connected_space
end