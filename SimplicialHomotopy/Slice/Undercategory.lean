/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The undercategory `C_{c/}` via décalage

For a simplicial set `X` and a vertex `c`, the undercategory `X_{c/}` of [Lur09, 1.2.9]
has as `m`-simplices the maps `Δ[0] ⋆ Δ[m] = Δ[m + 1] ⟶ X` whose restriction to the cone
point is `c`. We avoid the general join and define it by *décalage*: reindex `X` along
`⦋m⦌ ↦ ⦋m + 1⦌`, `f ↦ 0 ⋆ f` (`SimplexCategory.coneShiftHom`), and take the subcomplex
of simplices whose `0`-th vertex is `c`.

* `SSet.augShift ρ : Fin (a + 1) →o Fin (b + 1)` for `ρ : Fin a →o Fin b` : the map fixing `0`
  and acting as `ρ` on the remaining vertices; `SimplexCategory.coneShiftFun` is its case
  `a = m + 1`, `b = n + 1`.
* `SimplexCategory.coneShiftHom f : ⦋m + 1⦌ ⟶ ⦋n + 1⦌` : the map fixing `0` and acting as `f`
  on the remaining vertices (`Δ[0] ⋆ f`).
* `SSet.dec X` : the décalage, `(dec X)_m = X_{m + 1}`.
* `SSet.decVertex X` : the cone point of a simplex of `X.dec`; `SSet.decForget X : X.dec ⟶ X`,
  restriction along `δ 0`.
* `SSet.under X c` : the subcomplex of `X.dec` with cone point `c`; `SSet.underProj X c` the
  projection to `X`.

The identification with the join-based definition of [Lur09] is `Δ[0] ⋆ Δ[m] ≅ Δ[m + 1]`,
which is the *definition* of `coneShiftHom` on objects. The general cone `Δ[0] ⋆ (−)`
is built in `Join/Cone.lean`, where the universal property
`Hom(K, X_{c/}) ≅ Hom_c(Δ[0] ⋆ K, X)` is proved against this definition as
`SSet.coneHomEquiv`.

Implementation note: we deliberately do not package `⦋m⦌ ↦ ⦋m + 1⦌` as a functor
`SimplexCategory ⥤ SimplexCategory`, because then `coneShift.obj m` is not *reducibly*
`⦋m.len + 1⦌` and every `rw` on simplices of the décalage fails.
-/

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-- `Δ[0] ⋆ ρ` for `ρ : Fin a →o Fin b` (with `Fin 0 = ∅`): the map fixing `0` and acting as
`ρ` on the remaining vertices. `SimplexCategory.coneShiftFun` is the case where `a` and `b` are
successors. -/
def augShift {a b : ℕ} (ρ : Fin a →o Fin b) : Fin (a + 1) →o Fin (b + 1) where
  toFun := Fin.cases 0 (fun i ↦ (ρ i).succ)
  monotone' := by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        simp only [Fin.cases_succ]
        exact Fin.succ_le_succ_iff.2 (ρ.monotone (Fin.succ_le_succ_iff.1 hij))

@[simp] lemma augShift_zero {a b : ℕ} (ρ : Fin a →o Fin b) : augShift ρ 0 = 0 := rfl

@[simp] lemma augShift_succ {a b : ℕ} (ρ : Fin a →o Fin b) (i : Fin a) :
    augShift ρ i.succ = (ρ i).succ := rfl

end SSet

namespace SimplexCategory

/-- The map `Fin (m + 2) → Fin (n + 2)` fixing `0` and acting as `f` (shifted) elsewhere: the
case of `SSet.augShift` where both degrees are successors. -/
def coneShiftFun {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    Fin (m + 2) →o Fin (n + 2) :=
  SSet.augShift f

@[simp]
lemma coneShiftFun_zero {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    coneShiftFun f 0 = 0 := rfl

@[simp]
lemma coneShiftFun_succ {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    coneShiftFun f i.succ = (f i).succ := rfl

/-- `coneShiftFun` of a composite is the composite of the `coneShiftFun`s. -/
lemma coneShiftFun_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) :
    coneShiftFun (β.comp α) = (coneShiftFun β).comp (coneShiftFun α) := by
  refine OrderHom.ext _ _ (funext fun i ↦ ?_)
  induction i using Fin.cases <;> rfl

/-- `Δ[0] ⋆ f : ⦋m + 1⦌ ⟶ ⦋n + 1⦌` for `f : ⦋m⦌ ⟶ ⦋n⦌`. -/
def coneShiftHom {m n : SimplexCategory} (f : m ⟶ n) : ⦋m.len + 1⦌ ⟶ ⦋n.len + 1⦌ :=
  mkHom (coneShiftFun f.toOrderHom)

@[simp]
lemma coneShiftHom_id (m : SimplexCategory) : coneShiftHom (𝟙 m) = 𝟙 _ := by
  ext i : 3
  induction i using Fin.cases <;> simp [coneShiftHom, mkHom]

@[simp]
lemma coneShiftHom_comp {m n k : SimplexCategory} (f : m ⟶ n) (g : n ⟶ k) :
    coneShiftHom (f ≫ g) = coneShiftHom f ≫ coneShiftHom g := by
  ext i : 3
  induction i using Fin.cases <;> simp [coneShiftHom, mkHom]

/-- `coneShiftHom` fixes the cone point. -/
lemma const_zero_comp_coneShiftHom {m n : SimplexCategory} (f : m ⟶ n) :
    const ⦋0⦌ ⦋m.len + 1⦌ 0 ≫ coneShiftHom f = const ⦋0⦌ ⦋n.len + 1⦌ 0 := by
  ext i : 3
  rfl

/-- `δ 0 : ⦋m⦌ ⟶ ⦋m + 1⦌` is natural with respect to `coneShiftHom`. -/
lemma δ_zero_comp_coneShiftHom {m n : SimplexCategory} (f : m ⟶ n) :
    δ (0 : Fin (m.len + 2)) ≫ coneShiftHom f = f ≫ δ (0 : Fin (n.len + 2)) := by
  ext i : 3
  rfl

end SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- The décalage of `X`: `(dec X)_m = X_{m + 1}`, with simplicial operators acting on
the last `m + 1` vertices. -/
@[simps]
abbrev dec : SSet.{u} where
  obj m := X _⦋m.unop.len + 1⦌
  map f := X.map (SimplexCategory.coneShiftHom f.unop).op
  map_id m := by
    rw [unop_id, SimplexCategory.coneShiftHom_id, op_id, X.map_id]
  map_comp f g := by
    rw [unop_comp, SimplexCategory.coneShiftHom_comp, op_comp, X.map_comp]

/-- Restriction along `δ 0`, i.e. forgetting the cone point: `X.dec ⟶ X`. -/
@[simps]
def decForget : X.dec ⟶ X where
  app m := X.map (SimplexCategory.δ (0 : Fin (m.unop.len + 2))).op
  naturality m n f := by
    dsimp only [dec_map]
    rw [← X.map_comp, ← X.map_comp, ← op_comp, SimplexCategory.δ_zero_comp_coneShiftHom,
      op_comp]
    rfl

/-- The cone point of a simplex of `X.dec`. -/
def decVertex {m : SimplexCategoryᵒᵖ} (x : X.dec.obj m) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ ⦋m.unop.len + 1⦌ 0).op x

lemma decVertex_map {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (x : X.dec.obj m) :
    X.decVertex (X.dec.map f x) = X.decVertex x := by
  dsimp only [decVertex, dec_map]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_zero_comp_coneShiftHom]

/-- The undercategory `X_{c/}` as a subcomplex of the décalage: simplices with cone
point `c` ([Lur09, 1.2.9], via `Δ[0] ⋆ Δ[m] ≅ Δ[m + 1]`). -/
def under (c : X _⦋0⦌) : X.dec.Subcomplex where
  obj m := {x | X.decVertex x = c}
  map f x hx := by
    change X.decVertex (X.dec.map f x) = c
    rw [decVertex_map]
    exact hx

lemma mem_under_iff (c : X _⦋0⦌) {m : SimplexCategoryᵒᵖ} (x : X.dec.obj m) :
    x ∈ (X.under c).obj m ↔ X.decVertex x = c := Iff.rfl

/-- The projection `X_{c/} ⟶ X` (forgetting the cone point). -/
def underProj (c : X _⦋0⦌) : (X.under c : SSet.{u}) ⟶ X :=
  (X.under c).ι ≫ X.decForget

/-- The identity edge `id_c`, as a vertex of `X_{c/}`: the degenerate `1`-simplex `s₀ c`. -/
def underId (c : X _⦋0⦌) : (X.under c : SSet.{u}) _⦋0⦌ :=
  ⟨X.map (SimplexCategory.σ (0 : Fin 1)).op c, by
    change X.decVertex _ = c
    dsimp only [decVertex]
    rw [← Functor.map_comp_apply, ← op_comp]
    -- `const ⦋0⦌ ⦋1⦌ 0 ≫ σ 0 = 𝟙 ⦋0⦌`
    rw [SimplexCategory.Hom.ext_zero_left (SimplexCategory.const ⦋0⦌ ⦋0 + 1⦌ 0 ≫
      SimplexCategory.σ 0) (𝟙 _), op_id, X.map_id]
    rfl⟩

/-!
`X_{c/} ⟶ X` is a left fibration when `X` is a quasicategory ([Lur09, 2.1.2.2]). The proof needs
the cone `Δ[0] ⋆ (−)` and [Lur09, 2.1.2.3], so it is not in this file: the theorem is
`SSet.HTT.leftFibration_underProj` in `Cofinal/HTT.lean`, derived from
`SSet.leftFibration_underProj_of_innerAnodyne_cone` (`Join/Cone.lean`) and
`SSet.innerAnodyneConeOfLeftAnodyne` (2.1.2.3, `Join/ConeLifting.lean`).
-/

end SSet
