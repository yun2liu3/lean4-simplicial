/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Nerve.NerveHo

/-!
# The map `F_* = Fun(Δ[n], F)` and its strict fibers, for a map `F` to a nerve

`SimplicialHomotopy/Nerve/NerveHo.lean` proves that a map from a quasicategory to the nerve of
a small category is an inner fibration (`SSet.innerFibration_to_nerve`)
and draws two consequences for the *canonical* functor
`toNerveHo C : C ⟶ N(hC)` only. This file draws them for an arbitrary
`F : C ⟶ nerve A`:

* `SSet.innerFibration_ihomMap_of_nerve` : `F_* = Fun(Δ[n], F)` is an inner fibration
  (`Fun(Δ[n], −)` preserves inner fibrations, [Lur09, 2.3.2.5]);
* `SSet.strictFiber F y` : the **strict fiber**
  `F_*^{-1}(y) = Fun(Δ[n], C) ×_{Fun(Δ[n], N A)} Δ[0]` of `F_*` over an `n`-simplex `y` of `N A`;
* `SSet.quasicategory_strictFiber` : it is an ∞-category (the fiber of an inner fibration over
  a vertex is a quasicategory).

`SSet.fiberHo C y` of `NerveHo.lean` is `strictFiber (toNerveHo C) y`, and
`SSet.quasicategory_fiberHo` is the instance `quasicategory_strictFiber` in that case.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite Simplicial

namespace SSet

variable {X : SSet.{u}} [Quasicategory X] {A : Type u} [Category.{u} A]

/-- First consequence: if `F : C ⟶ N A` is a map from a quasicategory to the
nerve of a small category, then `F_* = Fun(Δ[n], F)` is an inner fibration. Indeed `F` is an
inner fibration (`innerFibration_to_nerve`) and `Fun(Δ[n], −)` preserves inner fibrations
([Lur09, 2.3.2.5]). -/
theorem innerFibration_ihomMap_of_nerve (F : X ⟶ nerve A) (K : SSet.{u}) :
    InnerFibration ((ihom K).map F) :=
  haveI := innerFibration_to_nerve F
  inferInstance

/-- For an arbitrary `F : C ⟶ N A`: the strict fiber
`F_*^{-1}(y) = Fun(Δ[n], C) ×_{Fun(Δ[n], N A)} Δ[0]` of `F_* : Fun(Δ[n], C) ⟶ Fun(Δ[n], N A)`
over the `n`-simplex `y` of `N A`, as the relative mapping space `Map_{N A}(Δ[n], C)`. -/
noncomputable def strictFiber (F : X ⟶ nerve A) {n : ℕ} (y : (nerve A) _⦋n⦌) : SSet.{u} :=
  relMap (yonedaEquiv.symm y) F

/-- Second consequence: the strict fibers of `F_*` are ∞-categories.
`F_*` is an inner fibration by `innerFibration_ihomMap_of_nerve`, inner fibrations are stable
under base change, and a simplicial set is a quasicategory iff its map to the terminal object
is an inner fibration. -/
instance quasicategory_strictFiber (F : X ⟶ nerve A) {n : ℕ} (y : (nerve A) _⦋n⦌) :
    Quasicategory (strictFiber F y) :=
  haveI := innerFibration_ihomMap_of_nerve F Δ[n]
  quasicategory_relMap_of_innerFibration F (yonedaEquiv.symm y)

end SSet
