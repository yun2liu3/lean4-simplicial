/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.Undercategory

/-!
# The coslice `X_{f/}` of a simplex, via the `p`-fold décalage

For a simplicial set `X` and a `p`-simplex `f : X _⦋p⦌`, the coslice `X_{f/}` of
[Lur09, §1.2.9] / Kerodon 017Y has as `m`-simplices the maps `Δ[p] ⋆ Δ[m] ⟶ X` whose
restriction to `Δ[p]` is `f`. Exactly as in `Slice/Undercategory.lean` (which is the case
`p = 0`), we avoid the general join in the *definition* and use the shift
`⦋m⦌ ↦ ⦋p + 1 + m⦌`, `α ↦ (𝟙_{⦋p⦌} ⋆ α)`; the identification with the join-based definition is
`SSet.stdSimplex.joinIso p m : Δ[p] ⋆ Δ[m] ≅ Δ[p + m + 1]` of `Join/JoinStd.lean`.

* `SimplexCategory.frontHom p m : ⦋p⦌ ⟶ ⦋p + 1 + m⦌` and
  `SimplexCategory.backHom p m : ⦋m⦌ ⟶ ⦋p + 1 + m⦌` : the two blocks.
* `SimplexCategory.shiftHom p f : ⦋p + 1 + m.len⦌ ⟶ ⦋p + 1 + n.len⦌` : `Δ[p] ⋆ f`.
* `SSet.decp X p` : the `p`-fold décalage, `(decp X p)_m = X_{p + 1 + m}`.
* `SSet.decpFront X p x : X _⦋p⦌` : the front face of a simplex of `decp X p`;
  `SSet.decpForget X p : X.decp p ⟶ X` : restriction along the back face.
* `SSet.coslice X f` : the subcomplex of `X.decp p` with front face `f`;
  `SSet.cosliceProj X f` : the projection to `X`.
* `SimplexCategory.frontShiftHom g m : ⦋p' + 1 + m⦌ ⟶ ⦋p + 1 + m⦌` : `g ⋆ Δ[m]`, for
  `g : ⦋p'⦌ ⟶ ⦋p⦌`.
* `SSet.decpRestrict X g : X.decp p ⟶ X.decp p'` and
  `SSet.cosliceRestrict X g f : X_{f/} ⟶ X_{g*f/}` : restriction along `g`.

For `p = 0` the degree `0 + 1 + m` agrees with `m + 1` as a natural number but not definitionally,
so `X.decp 0` and `X.dec` are canonically isomorphic rather than equal; the `p = 0` results of
`Slice/Undercategory.lean` are left as they are.
-/

universe u

open CategoryTheory Opposite Simplicial

namespace SimplexCategory

/-- The front block `Fin (p + 1) → Fin (p + 1 + (m + 1))` of `⦋p⦌ ⋆ ⦋m⦌`: the monotone map
under Mathlib's `Fin.castAddOrderEmb`. -/
def castAddOrderHom (p m : ℕ) : Fin (p + 1) →o Fin (p + 1 + (m + 1)) :=
  (Fin.castAddOrderEmb (m + 1)).toOrderHom

/-- The back block `Fin (m + 1) → Fin (p + 1 + (m + 1))` of `⦋p⦌ ⋆ ⦋m⦌`: the monotone map
under Mathlib's `Fin.natAddOrderEmb`. -/
def natAddOrderHom (p m : ℕ) : Fin (m + 1) →o Fin (p + 1 + (m + 1)) :=
  (Fin.natAddOrderEmb (p + 1)).toOrderHom

/-- The inclusion of the front `p + 1` vertices, `⦋p⦌ ⟶ ⦋p + 1 + m⦌`. -/
def frontHom (p m : ℕ) : ⦋p⦌ ⟶ ⦋p + 1 + m⦌ := mkHom (castAddOrderHom p m)

/-- The inclusion of the last `m + 1` vertices, `⦋m⦌ ⟶ ⦋p + 1 + m⦌`. -/
def backHom (p m : ℕ) : ⦋m⦌ ⟶ ⦋p + 1 + m⦌ := mkHom (natAddOrderHom p m)

/-- `𝟙_{⦋p⦌} ⋆ f` on vertices. -/
def shiftFun (p : ℕ) {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    Fin (p + 1 + (m + 1)) →o Fin (p + 1 + (n + 1)) where
  toFun := Fin.addCases (Fin.castAdd (n + 1)) (fun i ↦ Fin.natAdd (p + 1) (f i))
  monotone' i i' hii' := by
    induction i using Fin.addCases with
    | left i =>
      induction i' using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.le_def, Fin.val_castAdd]
        exact Fin.le_def.1 hii'
      | right i' =>
        simp only [Fin.addCases_left, Fin.addCases_right, Fin.le_def, Fin.val_castAdd,
          Fin.val_natAdd]
        have := i.isLt
        omega
    | right i =>
      induction i' using Fin.addCases with
      | left i' =>
        rw [Fin.le_def] at hii'
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hii'
        have := i'.isLt
        omega
      | right i' =>
        simp only [Fin.addCases_right, Fin.le_def, Fin.val_natAdd]
        rw [Fin.le_def] at hii'
        simp only [Fin.val_natAdd] at hii'
        have := f.monotone (show i ≤ i' from Fin.le_def.2 (by omega))
        have := Fin.le_def.1 this
        omega

@[simp]
lemma shiftFun_castAdd (p : ℕ) {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (p + 1)) :
    shiftFun p f (Fin.castAdd (m + 1) i) = Fin.castAdd (n + 1) i :=
  Fin.addCases_left (motive := fun _ ↦ Fin (p + 1 + (n + 1)))
    (left := Fin.castAdd (n + 1)) (right := fun j ↦ Fin.natAdd (p + 1) (f j)) i

@[simp]
lemma shiftFun_natAdd (p : ℕ) {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    shiftFun p f (Fin.natAdd (p + 1) i) = Fin.natAdd (p + 1) (f i) :=
  Fin.addCases_right (motive := fun _ ↦ Fin (p + 1 + (n + 1)))
    (left := Fin.castAdd (n + 1)) (right := fun j ↦ Fin.natAdd (p + 1) (f j)) i

/-- Two monotone maps out of `Fin (p + 1 + (m + 1))` agreeing on both blocks are equal. -/
lemma shiftFun_ext {p m N : ℕ} {g h : Fin (p + 1 + (m + 1)) →o Fin N}
    (hc : ∀ i : Fin (p + 1), g (Fin.castAdd (m + 1) i) = h (Fin.castAdd (m + 1) i))
    (hn : ∀ i : Fin (m + 1), g (Fin.natAdd (p + 1) i) = h (Fin.natAdd (p + 1) i)) : g = h :=
  OrderHom.ext _ _ (funext fun i ↦ Fin.addCases hc hn i)

/-- `𝟙_{⦋p⦌} ⋆ f : ⦋p + 1 + m⦌ ⟶ ⦋p + 1 + n⦌` for `f : ⦋m⦌ ⟶ ⦋n⦌`. -/
def shiftHom (p : ℕ) {m n : SimplexCategory} (f : m ⟶ n) : ⦋p + 1 + m.len⦌ ⟶ ⦋p + 1 + n.len⦌ :=
  mkHom (shiftFun p f.toOrderHom)

@[simp]
lemma shiftHom_id (p : ℕ) (m : SimplexCategory) : shiftHom p (𝟙 m) = 𝟙 _ :=
  Hom.ext _ _ (shiftFun_ext (fun i ↦ shiftFun_castAdd p _ i) (fun i ↦ shiftFun_natAdd p _ i))

@[simp]
lemma shiftHom_comp (p : ℕ) {m n k : SimplexCategory} (f : m ⟶ n) (g : n ⟶ k) :
    shiftHom p (f ≫ g) = shiftHom p f ≫ shiftHom p g :=
  Hom.ext _ _ (shiftFun_ext (fun i ↦ by simp [shiftHom, mkHom]) (fun i ↦ by simp [shiftHom, mkHom]))

/-- `shiftHom` fixes the front block. -/
lemma frontHom_comp_shiftHom (p : ℕ) {m n : SimplexCategory} (f : m ⟶ n) :
    frontHom p m.len ≫ shiftHom p f = frontHom p n.len :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ shiftFun_castAdd p f.toOrderHom i))

/-- `shiftHom` acts as `f` on the back block. -/
lemma backHom_comp_shiftHom (p : ℕ) {m n : SimplexCategory} (f : m ⟶ n) :
    backHom p m.len ≫ shiftHom p f = f ≫ backHom p n.len :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ shiftFun_natAdd p f.toOrderHom i))

/-- `g ⋆ 𝟙_{⦋m⦌}` on vertices, for `g : Fin (p' + 1) →o Fin (p + 1)`. -/
def frontShiftFun {p p' : ℕ} (g : Fin (p' + 1) →o Fin (p + 1)) (m : ℕ) :
    Fin (p' + 1 + (m + 1)) →o Fin (p + 1 + (m + 1)) where
  toFun := Fin.addCases (fun i ↦ Fin.castAdd (m + 1) (g i)) (Fin.natAdd (p + 1))
  monotone' i i' hii' := by
    induction i using Fin.addCases with
    | left i =>
      induction i' using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.le_def, Fin.val_castAdd]
        exact Fin.le_def.1 (g.monotone (Fin.le_def.2 (by
          have := Fin.le_def.1 hii'
          simpa only [Fin.val_castAdd] using this)))
      | right i' =>
        simp only [Fin.addCases_left, Fin.addCases_right, Fin.le_def, Fin.val_castAdd,
          Fin.val_natAdd]
        have := (g i).isLt
        omega
    | right i =>
      induction i' using Fin.addCases with
      | left i' =>
        rw [Fin.le_def] at hii'
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hii'
        have := i'.isLt
        omega
      | right i' =>
        simp only [Fin.addCases_right, Fin.le_def, Fin.val_natAdd]
        rw [Fin.le_def] at hii'
        simp only [Fin.val_natAdd] at hii'
        omega

@[simp]
lemma frontShiftFun_castAdd {p p' : ℕ} (g : Fin (p' + 1) →o Fin (p + 1)) (m : ℕ)
    (i : Fin (p' + 1)) :
    frontShiftFun g m (Fin.castAdd (m + 1) i) = Fin.castAdd (m + 1) (g i) :=
  Fin.addCases_left (motive := fun _ ↦ Fin (p + 1 + (m + 1)))
    (left := fun j ↦ Fin.castAdd (m + 1) (g j)) (right := Fin.natAdd (p + 1)) i

@[simp]
lemma frontShiftFun_natAdd {p p' : ℕ} (g : Fin (p' + 1) →o Fin (p + 1)) (m : ℕ)
    (i : Fin (m + 1)) :
    frontShiftFun g m (Fin.natAdd (p' + 1) i) = Fin.natAdd (p + 1) i :=
  Fin.addCases_right (motive := fun _ ↦ Fin (p + 1 + (m + 1)))
    (left := fun j ↦ Fin.castAdd (m + 1) (g j)) (right := Fin.natAdd (p + 1)) i

/-- `g ⋆ 𝟙_{⦋m⦌} : ⦋p' + 1 + m⦌ ⟶ ⦋p + 1 + m⦌` for `g : ⦋p'⦌ ⟶ ⦋p⦌`. -/
def frontShiftHom {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (m : ℕ) : ⦋p' + 1 + m⦌ ⟶ ⦋p + 1 + m⦌ :=
  mkHom (frontShiftFun g.toOrderHom m)

/-- `frontShiftHom` acts as `g` on the front block. -/
lemma frontHom_comp_frontShiftHom {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (m : ℕ) :
    frontHom p' m ≫ frontShiftHom g m = g ≫ frontHom p m :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ frontShiftFun_castAdd g.toOrderHom m i))

/-- `frontShiftHom` fixes the back block. -/
lemma backHom_comp_frontShiftHom {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (m : ℕ) :
    backHom p' m ≫ frontShiftHom g m = backHom p m :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ frontShiftFun_natAdd g.toOrderHom m i))

/-- The two shifts commute: `(g ⋆ 𝟙) ≫ (𝟙 ⋆ f) = (𝟙 ⋆ f) ≫ (g ⋆ 𝟙)`. -/
lemma frontShiftHom_comp_shiftHom {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) {m n : SimplexCategory}
    (f : m ⟶ n) :
    frontShiftHom g m.len ≫ shiftHom p f = shiftHom p' f ≫ frontShiftHom g n.len :=
  Hom.ext _ _ (shiftFun_ext (fun i ↦ by simp [shiftHom, frontShiftHom, mkHom])
    (fun i ↦ by simp [shiftHom, frontShiftHom, mkHom]))

end SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- The `p`-fold décalage of `X`: `(decp X p)_m = X_{p + 1 + m}`, with simplicial operators
acting on the last `m + 1` vertices. -/
@[simps]
abbrev decp (p : ℕ) : SSet.{u} where
  obj m := X _⦋p + 1 + m.unop.len⦌
  map f := X.map (SimplexCategory.shiftHom p f.unop).op
  map_id m := by rw [unop_id, SimplexCategory.shiftHom_id, op_id, X.map_id]
  map_comp f g := by rw [unop_comp, SimplexCategory.shiftHom_comp, op_comp, X.map_comp]

/-- Restriction along the back face: `X.decp p ⟶ X`. -/
@[simps]
def decpForget (p : ℕ) : X.decp p ⟶ X where
  app m := X.map (SimplexCategory.backHom p m.unop.len).op
  naturality m n f := by
    dsimp only [decp_map]
    rw [← X.map_comp, ← X.map_comp, ← op_comp, SimplexCategory.backHom_comp_shiftHom, op_comp]
    rfl

/-- The front face of a simplex of `X.decp p`. -/
def decpFront (p : ℕ) {m : SimplexCategoryᵒᵖ} (x : (X.decp p).obj m) : X _⦋p⦌ :=
  X.map (SimplexCategory.frontHom p m.unop.len).op x

lemma decpFront_map (p : ℕ) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (x : (X.decp p).obj m) :
    X.decpFront p ((X.decp p).map f x) = X.decpFront p x := by
  dsimp only [decpFront, decp_map]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.frontHom_comp_shiftHom]

/-- The coslice `X_{f/}` of a `p`-simplex `f`, as a subcomplex of the `p`-fold décalage:
the simplices whose front face is `f` (Kerodon 017Y, [Lur09, §1.2.9]). -/
def coslice {p : ℕ} (f : X _⦋p⦌) : (X.decp p).Subcomplex where
  obj m := {x | X.decpFront p x = f}
  map g x hx := by
    change X.decpFront p ((X.decp p).map g x) = f
    rw [decpFront_map]
    exact hx

lemma mem_coslice_iff {p : ℕ} (f : X _⦋p⦌) {m : SimplexCategoryᵒᵖ} (x : (X.decp p).obj m) :
    x ∈ (X.coslice f).obj m ↔ X.decpFront p x = f := Iff.rfl

/-- The projection `X_{f/} ⟶ X`. -/
def cosliceProj {p : ℕ} (f : X _⦋p⦌) : (X.coslice f : SSet.{u}) ⟶ X :=
  (X.coslice f).ι ≫ X.decpForget p

@[simp]
lemma cosliceProj_app {p : ℕ} (f : X _⦋p⦌) {m : SimplexCategoryᵒᵖ}
    (x : (X.coslice f : SSet.{u}).obj m) :
    (X.cosliceProj f).app m x = X.map (SimplexCategory.backHom p m.unop.len).op x.1 := rfl

/-- Restriction along `g ⋆ 𝟙`: the map of décalages `X.decp p ⟶ X.decp p'` induced by
`g : ⦋p'⦌ ⟶ ⦋p⦌`. -/
@[simps]
def decpRestrict {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) : X.decp p ⟶ X.decp p' where
  app m := X.map (SimplexCategory.frontShiftHom g m.unop.len).op
  naturality m n f := by
    dsimp only [decp_map]
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp,
      SimplexCategory.frontShiftHom_comp_shiftHom]

lemma decpFront_decpRestrict {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) {m : SimplexCategoryᵒᵖ}
    (x : (X.decp p).obj m) :
    X.decpFront p' ((X.decpRestrict g).app m x) = X.map g.op (X.decpFront p x) := by
  change X.map (SimplexCategory.frontHom p' m.unop.len).op
      (X.map (SimplexCategory.frontShiftHom g m.unop.len).op x) =
    X.map g.op (X.map (SimplexCategory.frontHom p m.unop.len).op x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    SimplexCategory.frontHom_comp_frontShiftHom]

lemma decpForget_decpRestrict {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) :
    X.decpRestrict g ≫ X.decpForget p' = X.decpForget p := by
  refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  change X.map (SimplexCategory.backHom p' m.unop.len).op
    (X.map (SimplexCategory.frontShiftHom g m.unop.len).op x) = _
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.backHom_comp_frontShiftHom]
  rfl

lemma range_coslice_ι_comp_decpRestrict {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (f : X _⦋p⦌) :
    Subcomplex.range ((X.coslice f).ι ≫ X.decpRestrict g) ≤ X.coslice (X.map g.op f) := by
  rintro k _ ⟨x, rfl⟩
  change X.decpFront p' ((X.decpRestrict g).app k x.1) = X.map g.op f
  rw [decpFront_decpRestrict, x.2]

/-- The restriction map between coslices, `X_{f/} ⟶ X_{g*f/}` for `g : ⦋p'⦌ ⟶ ⦋p⦌`
(the restriction map of Kerodon 4.3.6.8, for a simplex). -/
def cosliceRestrict {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (f : X _⦋p⦌) :
    (X.coslice f : SSet.{u}) ⟶ (X.coslice (X.map g.op f) : SSet.{u}) :=
  Subcomplex.lift ((X.coslice f).ι ≫ X.decpRestrict g)
    (X.range_coslice_ι_comp_decpRestrict g f)

@[simp]
lemma cosliceRestrict_ι {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (f : X _⦋p⦌) :
    X.cosliceRestrict g f ≫ (X.coslice (X.map g.op f)).ι =
      (X.coslice f).ι ≫ X.decpRestrict g := rfl

/-- The restriction maps are compatible with the projections to `X`. -/
lemma cosliceRestrict_comp_cosliceProj {p p' : ℕ} (g : ⦋p'⦌ ⟶ ⦋p⦌) (f : X _⦋p⦌) :
    X.cosliceRestrict g f ≫ X.cosliceProj (X.map g.op f) = X.cosliceProj f := by
  rw [cosliceProj, ← Category.assoc, cosliceRestrict_ι, Category.assoc,
    decpForget_decpRestrict, cosliceProj]

end SSet
