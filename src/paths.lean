import gluing
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
