/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.VanKampen

/-!
# Universal colimits in `Type` and in `SSet`

A colimit cocone is *universal* (`CategoryTheory.IsUniversalColimit`) if it is stable under
pullback: any cocone obtained by pulling it back along a morphism into the colimit point is
again a colimit. In a presheaf topos every colimit is universal; this file proves the two
instances needed downstream, for `Type u` and for simplicial sets.

* `CategoryTheory.Limits.Types.ι_app_eq_of_eqvGen` : two elements of a diagram in `Type u`
  connected by the zig-zag relation generating the colimit have the same image under any
  cocone.
* `CategoryTheory.Limits.Types.isUniversalColimit` : every colimit in `Type u` is universal.
  The proof is elementwise: joint surjectivity of the pulled-back cocone follows from joint
  surjectivity of the original one plus the pullback squares, and the zig-zag connecting two
  elements with the same image is lifted step by step through the pullback squares.
* `CategoryTheory.Limits.isUniversalColimit_of_evaluation_types` : colimits in a functor
  category `C ⥤ Type u` are universal, by evaluating objectwise.
* `SSet.isUniversalColimit` : every colimit in `SSet.{u}` is universal.

The last two statements assume `HasColimitsOfShape J (Type u)`, which is automatic when the
indexing category `J` is `u`-small (in particular for `J = ℕ` and `J = Discrete ι` with
`ι : Type u`); it is what makes the evaluation functors preserve the colimit `c`.
-/

universe w w' u

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]

namespace Types

/-- Elements of a diagram in `Type u` related by the zig-zag relation `F.ColimitTypeRel`
have the same image under any cocone. -/
lemma ι_app_eq_of_eqvGen {F : J ⥤ Type u} (c : Cocone F) {p q : Σ j, F.obj j}
    (h : Relation.EqvGen F.ColimitTypeRel p q) : c.ι.app p.1 p.2 = c.ι.app q.1 q.2 := by
  induction h with
  | rel p q hpq =>
    obtain ⟨g, hg⟩ := hpq
    rw [hg, ← types_comp_apply (F.map g) (c.ι.app q.1), c.w g]
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Colimits in `Type u` are universal. -/
theorem isUniversalColimit {F : J ⥤ Type u} (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e _ H
  have hf : ∀ (j : J) (x : F'.obj j), c.ι.app j (α.app j x) = f (c'.ι.app j x) := fun j x ↦ by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e j) x
    simpa using this
  -- Lifting a zig-zag in `F` to a zig-zag in `F'` through the pullback squares.
  have key : ∀ {p q : Σ j, F.obj j}, Relation.EqvGen F.ColimitTypeRel p q →
      ∀ (x : F'.obj p.1) (x' : F'.obj q.1), α.app _ x = p.2 → α.app _ x' = q.2 →
        c'.ι.app _ x = c'.ι.app _ x' →
        Relation.EqvGen F'.ColimitTypeRel ⟨p.1, x⟩ ⟨q.1, x'⟩ := by
    intro p q h
    induction h with
    | rel p q hpq =>
      obtain ⟨g, hg⟩ := hpq
      intro x x' hx hx' hxx'
      refine .rel _ _ ⟨g, ?_⟩
      dsimp only
      apply Types.ext_of_isPullback (H q.1)
      · rw [← hxx', ← types_comp_apply (F'.map g) (c'.ι.app q.1), c'.w g]
      · rw [← types_comp_apply (F'.map g) (α.app q.1), α.naturality g, types_comp_apply,
          hx, hx']
        exact hg
    | refl p =>
      intro x x' hx hx' hxx'
      obtain rfl : x = x' := Types.ext_of_isPullback (H p.1) hxx' (hx.trans hx'.symm)
      exact .refl _
    | symm p q _ ih =>
      intro x x' hx hx' hxx'
      exact .symm _ _ (ih x' x hx' hx hxx'.symm)
    | trans p q r hpq _ ih₁ ih₂ =>
      intro x x' hx hx' hxx'
      obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback (H q.1) (c'.ι.app p.1 x) q.2
        (by rw [← hf, hx]; exact ι_app_eq_of_eqvGen c hpq)
      exact .trans _ _ _ (ih₁ x y hx hy₂ hy₁.symm) (ih₂ y x' hy₂ hx' (hy₁.trans hxx'))
  have hc' := (Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  refine ⟨⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩⟩
  · obtain ⟨j, x, rfl⟩ := F'.ιColimitType_jointly_surjective a
    obtain ⟨j', x', rfl⟩ := F'.ιColimitType_jointly_surjective b
    simp only [Functor.descColimitType_ιColimitType_apply,
      Functor.coconeTypesEquiv_symm_apply_ι] at hab
    have h₁ : F.ιColimitType j (α.app j x) = F.ιColimitType j' (α.app j' x') := by
      apply hc'.bijective.1
      simp only [Functor.descColimitType_ιColimitType_apply,
        Functor.coconeTypesEquiv_symm_apply_ι]
      rw [hf, hf, hab]
    exact (F'.ιColimitType_eq_iff x x').2
      (key ((F.ιColimitType_eq_iff _ _).1 h₁) x x' rfl rfl hab)
  · obtain ⟨j, z, hz⟩ := Types.jointly_surjective F hc (f y)
    obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback (H j) y z hz.symm
    exact ⟨F'.ιColimitType j x, by rw [Functor.descColimitType_ιColimitType_apply]; exact hx⟩

end Types

/-- Colimits in a functor category with values in `Type u` are universal: the evaluation
functors preserve and jointly reflect colimits, and pullbacks are computed objectwise. -/
theorem isUniversalColimit_of_evaluation_types {C : Type*} [Category* C]
    [HasColimitsOfShape J (Type u)] (F : J ⥤ C ⥤ Type u) (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e hα H
  refine ⟨evaluationJointlyReflectsColimits _ fun x ↦ ?_⟩
  refine (Types.isUniversalColimit (((evaluation C (Type u)).obj x).mapCocone c)
    (isColimitOfPreserves _ hc) (((evaluation C (Type u)).obj x).mapCocone c')
    (Functor.whiskerRight α _) (((evaluation C (Type u)).obj x).map f) ?_ (hα.whiskerRight _)
    fun j ↦ (H j).map ((evaluation C (Type u)).obj x)).some
  exact NatTrans.ext (funext fun j ↦ by
    simpa using NatTrans.congr_app (NatTrans.congr_app e j) x)

end CategoryTheory.Limits

/-- Colimits in `SSet.{u}` are universal. -/
theorem SSet.isUniversalColimit {J : Type w} [Category.{w'} J] [HasColimitsOfShape J (Type u)]
    {F : J ⥤ SSet.{u}} (c : Cocone F) (hc : IsColimit c) : IsUniversalColimit c :=
  isUniversalColimit_of_evaluation_types F c hc
