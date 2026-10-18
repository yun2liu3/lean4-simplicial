/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# Maps from a quasicategory to the nerve of a thin category are inner fibrations

If `X` is a quasicategory and
`C` is a *thin* category (at most one morphism between any two objects, e.g. the category
attached to a preorder or a poset), then every map `F : X ⟶ nerve C` is an inner fibration.

Proof: given an inner horn `Λ[n + 2, i]` and a commutative square
`u : Λ[n + 2, i] ⟶ X`, `v : Δ[n + 2] ⟶ nerve C` with `u ≫ F = Λ[n + 2, i].ι ≫ v`,
horn filling in `X` gives `σ : Δ[n + 2] ⟶ X` with `u = Λ[n + 2, i].ι ≫ σ`.
Both `σ ≫ F` and `v` are `(n + 2)`-simplices of `nerve C`; such a simplex is determined by
its vertices (`nerve.ext_of_isThin`), and every vertex of `Δ[n + 2]` lies in the horn
(`horn_obj_zero`, since `n + 2 ≥ 2`), where `σ ≫ F` and `v` agree.

* `SSet.yonedaEquiv_nerve_obj` : the `k`-th vertex of `yonedaEquiv f` for
  `f : Δ[m] ⟶ nerve C` is `f` evaluated at the vertex `k` of `Δ[m]`.
* `SSet.innerFibrations_to_nerve_of_isThin`, `SSet.innerFibration_to_nerve_of_isThin` :
  the statement (`innerFibrations F`, resp. `InnerFibration F`).
* `SSet.innerFibrations_to_nerve_preorder` : the special case of a preorder/poset `P`.
* `SSet.quasicategory_pullback_to_nerve_of_isThin`,
  `SSet.quasicategory_fiber_to_nerve_of_isThin` : the pullback of such an `F` along a map
  from a quasicategory (in particular every fiber over a vertex) is a quasicategory.
* `SSet.quasicategory_stdSimplex` : `Δ[n]` is a quasicategory (via `stdSimplex.isoNerve`).
-/

universe u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace SSet

section Vertices

variable {C : Type u} [Category.{u} C]

/-- The vertex `k` of `Δ[m]`, as a `0`-simplex, is `objEquiv.symm` of the constant map. -/
lemma obj₀Equiv_symm_eq_objEquiv_symm_const {m : ℕ} (k : Fin (m + 1)) :
    stdSimplex.obj₀Equiv.symm k =
      stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋m⦌ k) :=
  rfl

/-- The `k`-th object of the `m`-simplex `yonedaEquiv f` of `nerve C` (`f : Δ[m] ⟶ nerve C`)
is the value of `f` on the vertex `k` of `Δ[m]`. -/
lemma yonedaEquiv_nerve_obj {m : ℕ} (f : Δ[m] ⟶ nerve C) (k : Fin (m + 1)) :
    (yonedaEquiv f).obj k =
      nerveEquiv (f.app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm k)) := by
  rw [obj₀Equiv_symm_eq_objEquiv_symm_const, ← yonedaEquiv_map, ← yonedaEquiv_comp,
    ← yonedaEquiv_naturality]
  rfl

end Vertices

section Thin

variable {X : SSet.{u}} [Quasicategory X] {C : Type u} [Category.{u} C] [Quiver.IsThin C]

/-- A map from a quasicategory to the nerve of a thin category
(e.g. the nerve of a poset) is an inner fibration (`MorphismProperty` form). -/
theorem innerFibrations_to_nerve_of_isThin (F : X ⟶ nerve C) : innerFibrations F := by
  rintro _ _ _ ⟨i, h0, hn⟩
  constructor
  intro u v sq
  obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling h0 hn u
  refine ⟨⟨⟨σ, hσ.symm, ?_⟩⟩⟩
  have hw : Λ[_ + 2, i].ι ≫ σ ≫ F = Λ[_ + 2, i].ι ≫ v := by
    rw [← Category.assoc, ← hσ, sq.w]
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext k
  rw [yonedaEquiv_nerve_obj, yonedaEquiv_nerve_obj]
  congr 1
  -- the vertex `k` lies in the horn since `n + 2 ≥ 2`
  have hk : stdSimplex.obj₀Equiv.symm k ∈ Λ[_ + 2, i].obj (op ⦋0⦌) := by simp
  exact congrArg (fun g ↦ g.app (op ⦋0⦌) ⟨stdSimplex.obj₀Equiv.symm k, hk⟩) hw

/-- Class form: a map from a quasicategory to the nerve of a thin category
is an inner fibration. -/
theorem innerFibration_to_nerve_of_isThin (F : X ⟶ nerve C) : InnerFibration F :=
  ⟨innerFibrations_to_nerve_of_isThin F⟩

end Thin

section Preorder

variable {X : SSet.{u}} [Quasicategory X] {P : Type u} [Preorder P]

/-- The category attached to a preorder is thin (found by instance search; recorded here so
that the specialization to posets is visibly available). -/
example : Quiver.IsThin P := inferInstance

/-- The case of a poset (or preorder) `P`: a map `F : X ⟶ nerve P` from a
quasicategory is an inner fibration. -/
theorem innerFibrations_to_nerve_preorder (F : X ⟶ nerve P) : innerFibrations F :=
  innerFibrations_to_nerve_of_isThin F

/-- The case of a poset (or preorder) `P`, class form. -/
theorem innerFibration_to_nerve_preorder (F : X ⟶ nerve P) : InnerFibration F :=
  innerFibration_to_nerve_of_isThin F

end Preorder

section Fibers

variable {X : SSet.{u}} [Quasicategory X] {C : Type u} [Category.{u} C] [Quiver.IsThin C]

/-- A base change of a map `F` from a quasicategory to the nerve of a thin category is an inner
fibration: given a pullback square with right edge `F`, the left edge is in `innerFibrations`. -/
theorem innerFibrations_of_isPullback_to_nerve_of_isThin {Y X' : SSet.{u}}
    (F : X ⟶ nerve C) {f : Y ⟶ nerve C} {F' : X' ⟶ Y} {g : X' ⟶ X}
    (sq : IsPullback g F' F f) : innerFibrations F' :=
  MorphismProperty.of_isPullback sq (innerFibrations_to_nerve_of_isThin F)

/-- The standard simplex `Δ[n]` is a quasicategory: it is isomorphic to the nerve of the
linear order `ULift (Fin (n + 1))` (`stdSimplex.isoNerve`). -/
instance quasicategory_stdSimplex (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) := by
  rw [quasicategory_iff_innerFibration, innerFibration_iff]
  have h := (quasicategory_iff_innerFibration (nerve (ULift.{u} (Fin (n + 1))))).1 inferInstance
  rw [innerFibration_iff] at h
  refine (innerFibrations.arrow_mk_iso_iff (Arrow.isoMk (f := Arrow.mk (terminal.from Δ[n]))
    (g := Arrow.mk (terminal.from (nerve (ULift.{u} (Fin (n + 1))))))
    (stdSimplex.isoNerve.{u} n) (Iso.refl _) (terminalIsTerminal.hom_ext _ _))).2 h

/-- The pullback of a map `F : X ⟶ nerve C` (with `X` a quasicategory, `C` thin) along
any map `f : Y ⟶ nerve C` from a quasicategory `Y` is a quasicategory. -/
theorem quasicategory_pullback_to_nerve_of_isThin (F : X ⟶ nerve C)
    {Y : SSet.{u}} [Quasicategory Y] (f : Y ⟶ nerve C) : Quasicategory (pullback F f) := by
  have : InnerFibration (pullback.snd F f) :=
    ⟨innerFibrations.pullback_snd F f (innerFibrations_to_nerve_of_isThin F)⟩
  exact quasicategory_of_innerFibration (pullback.snd F f)

/-- Every fiber of a map `F : X ⟶ nerve C` (with `X` a quasicategory, `C` thin) over a
vertex `c : Δ[0] ⟶ nerve C` is a quasicategory. -/
theorem quasicategory_fiber_to_nerve_of_isThin (F : X ⟶ nerve C)
    (c : Δ[0] ⟶ nerve C) : Quasicategory (pullback F c) :=
  quasicategory_pullback_to_nerve_of_isThin F c

end Fibers

end SSet
