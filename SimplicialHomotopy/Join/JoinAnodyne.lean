/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.JoinHorn

/-!
# The join of two subcomplexes, and the generating case of the pushout-join lemma

`Join/JoinHorn.lean` describes the subcomplex `A₀ ⋆ B₀` of `A ⋆ B`
(`SSet.Subcomplex.joinSub`) and identifies the union `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])`
with a horn of `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]`. This file adds the two things needed to *use* that
identification:

* `SSet.Subcomplex.joinSubIso A₀ B₀ : A₀ ⋆ B₀ ≅ (joinSub A₀ B₀ : SSet)` — the join of the two
  subcomplexes *as a simplicial set* is the subcomplex `joinSub A₀ B₀` of `A ⋆ B`, with the
  variants `joinSubRightIso` (`A₀ = ⊤`) and `joinSubLeftIso` (`B₀ = ⊤`) that keep the ambient
  factor; everything is expressed through `SSet.Subcomplex.augLift` of `Join/Cone.lean`.
* `SSet.Subcomplex.joinSub_inf` — the intersection `(A ⋆ B₀) ∩ (A₀ ⋆ B) = A₀ ⋆ B₀`, which makes
  the union a `Subcomplex.BicartSq`, i.e. a pushout.
* `SSet.innerAnodyneExtensions_joinSub_sup` — **the generating case of the join form of
  [Lur09, Lemma 2.1.2.3]**: for `i < Fin.last (n+1)` the inclusion
  `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1]) ↪ Δ[p] ⋆ Δ[n+1]` is inner anodyne, being an inner
  horn inclusion transported along `SSet.stdSimplex.joinIso`.

The last statement is what makes the coslice restriction `X_{f/} ⟶ X_{f₀/}` of a simplex
`f : Δ[p] ⟶ X` a left fibration (Kerodon 4.3.6.8, `Slice/CosliceFibration.lean`).
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

namespace Subcomplex

variable {A B : SSet.{u}}

/-! ### `A₀ ⋆ B₀` as a simplicial set and as a subcomplex -/

/-- The morphism `A₀ ⋆ B₀ ⟶ joinSub A₀ B₀` induced by the two inclusions (an isomorphism,
inverse `joinSubLift`). -/
def joinToSub (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) (B₀ : SSet.{u}) ⟶ (joinSub A₀ B₀ : SSet.{u}) :=
  Subcomplex.lift (joinMap A₀.ι B₀.ι) (by
    rintro n _ ⟨s, rfl⟩
    exact ⟨augMem_augHom_ι A₀ s.x, augMem_augHom_ι B₀ s.y⟩)

@[reassoc (attr := simp)]
lemma joinToSub_ι (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinToSub A₀ B₀ ≫ (joinSub A₀ B₀).ι = joinMap A₀.ι B₀.ι := rfl

/-- The morphism `joinSub A₀ B₀ ⟶ A₀ ⋆ B₀` lifting the two blocks of a simplex into the
subcomplexes (an isomorphism, inverse `joinToSub`). -/
def joinSubLift (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    (joinSub A₀ B₀ : SSet.{u}) ⟶ join (A₀ : SSet.{u}) (B₀ : SSet.{u}) where
  app _ := ↾fun s ↦ ⟨s.1.j, s.1.k, s.1.hjk, A₀.augLift s.1.x s.2.1, B₀.augLift s.1.y s.2.2⟩
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ ↦ by
    refine JoinSimplex.ext_of_j_eq ?_ ?_ ?_
    · rfl
    · exact heq_of_eq (augLift_augMap A₀ _ _ _)
    · exact heq_of_eq (augLift_augMap B₀ _ _ _)

@[reassoc]
lemma joinSubLift_joinMap_ι (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinSubLift A₀ B₀ ≫ joinMap A₀.ι B₀.ι = (joinSub A₀ B₀).ι :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦ by
    refine JoinSimplex.ext_of_j_eq ?_ ?_ ?_
    · rfl
    · exact heq_of_eq (augHom_ι_augLift A₀ _ _)
    · exact heq_of_eq (augHom_ι_augLift B₀ _ _))

lemma joinToSub_joinSubLift (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinToSub A₀ B₀ ≫ joinSubLift A₀ B₀ = 𝟙 _ :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦ by
    refine JoinSimplex.ext_of_j_eq ?_ ?_ ?_
    · rfl
    · exact heq_of_eq (augLift_augHom_ι A₀ _)
    · exact heq_of_eq (augLift_augHom_ι B₀ _))

lemma joinSubLift_joinToSub (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinSubLift A₀ B₀ ≫ joinToSub A₀ B₀ = 𝟙 _ := by
  rw [← cancel_mono (joinSub A₀ B₀).ι, Category.assoc, joinToSub_ι, joinSubLift_joinMap_ι,
    Category.id_comp]

/-- The join of two subcomplexes, as a simplicial set, is the subcomplex `joinSub A₀ B₀`
of `A ⋆ B`. -/
@[simps]
def joinSubIso (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) (B₀ : SSet.{u}) ≅ (joinSub A₀ B₀ : SSet.{u}) where
  hom := joinToSub A₀ B₀
  inv := joinSubLift A₀ B₀
  hom_inv_id := joinToSub_joinSubLift A₀ B₀
  inv_hom_id := joinSubLift_joinToSub A₀ B₀

/-- `A ⋆ B₀` is the subcomplex `joinSub ⊤ B₀` of `A ⋆ B`. -/
def joinSubRightIso (A : SSet.{u}) (B₀ : B.Subcomplex) :
    join A (B₀ : SSet.{u}) ≅ (joinSub (⊤ : A.Subcomplex) B₀ : SSet.{u}) :=
  (joinMapIso (topIso A).symm (Iso.refl _)).trans (joinSubIso ⊤ B₀)

@[reassoc]
lemma joinSubRightIso_hom_ι (A : SSet.{u}) (B₀ : B.Subcomplex) :
    (joinSubRightIso A B₀).hom ≫ (joinSub (⊤ : A.Subcomplex) B₀).ι = joinMap (𝟙 A) B₀.ι := by
  show (joinMap (topIso A).inv (Iso.refl (B₀ : SSet.{u})).hom ≫ joinToSub ⊤ B₀) ≫ _ = _
  rw [Category.assoc, joinToSub_ι, ← joinMap_comp, Iso.refl_hom, Category.id_comp,
    ← topIso_hom, Iso.inv_hom_id]

/-- `A₀ ⋆ B` is the subcomplex `joinSub A₀ ⊤` of `A ⋆ B`. -/
def joinSubLeftIso (A₀ : A.Subcomplex) (B : SSet.{u}) :
    join (A₀ : SSet.{u}) B ≅ (joinSub A₀ (⊤ : B.Subcomplex) : SSet.{u}) :=
  (joinMapIso (Iso.refl _) (topIso B).symm).trans (joinSubIso A₀ ⊤)

@[reassoc]
lemma joinSubLeftIso_hom_ι (A₀ : A.Subcomplex) (B : SSet.{u}) :
    (joinSubLeftIso A₀ B).hom ≫ (joinSub A₀ (⊤ : B.Subcomplex)).ι = joinMap A₀.ι (𝟙 B) := by
  show (joinMap (Iso.refl (A₀ : SSet.{u})).hom (topIso B).inv ≫ joinToSub A₀ ⊤) ≫ _ = _
  rw [Category.assoc, joinToSub_ι, ← joinMap_comp, Iso.refl_hom, Category.id_comp,
    ← topIso_hom, Iso.inv_hom_id]

/-- The intersection of two joins of subcomplexes is the join of the intersections; with
`A₁ = ⊤` and `B₀ = ⊤` this says `(A ⋆ B₁) ∩ (A₀ ⋆ B) = A₀ ⋆ B₁`. -/
lemma joinSub_inf (A₀ A₁ : A.Subcomplex) (B₀ B₁ : B.Subcomplex) :
    joinSub A₀ B₀ ⊓ joinSub A₁ B₁ = joinSub (A₀ ⊓ A₁) (B₀ ⊓ B₁) :=
  le_antisymm
    (fun _ _ hs ↦ ⟨(augMem_inf _ _ _).2 ⟨hs.1.1, hs.2.1⟩, (augMem_inf _ _ _).2 ⟨hs.1.2, hs.2.2⟩⟩)
    (fun _ _ hs ↦ ⟨⟨((augMem_inf _ _ _).1 hs.1).1, ((augMem_inf _ _ _).1 hs.2).1⟩,
      ⟨((augMem_inf _ _ _).1 hs.1).2, ((augMem_inf _ _ _).1 hs.2).2⟩⟩)

end Subcomplex

/-! ### The generating case of the join form of [Lur09, 2.1.2.3] -/

open stdSimplex in
/-- **The generating case of the join form of [Lur09, Lemma 2.1.2.3]**: for `i < Fin.last (n+1)`
the inclusion `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1]) ↪ Δ[p] ⋆ Δ[n+1]` is inner anodyne. By
`SSet.stdSimplex.preimage_horn_joinIso` it *is* the horn inclusion at the back vertex
`p + 1 + i` of `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]`, and that horn is inner precisely because the vertex
is neither the first (`0 < p + 1 + i`) nor the last (`p + 1 + i < p + n + 2`, i.e.
`i < Fin.last (n+1)`). -/
theorem innerAnodyneExtensions_joinSub_sup (p n : ℕ) (i : Fin (n + 1 + 1))
    (hi : i < Fin.last (n + 1)) :
    innerAnodyneExtensions
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) (horn (n + 1) i) ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι := by
  rw [← stdSimplex.preimage_horn_joinIso p n i]
  refine (innerAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.preimageIso _ (stdSimplex.joinIso.{u} p (n + 1)))
      (stdSimplex.joinIso.{u} p (n + 1)) rfl)).2 (innerAnodyneExtensions.horn_ι ?_ ?_)
  · rw [Fin.lt_def]
    show 0 < p + 1 + (i : ℕ)
    omega
  · rw [Fin.lt_def] at hi ⊢
    simp only [Fin.val_last] at hi ⊢
    show p + 1 + (i : ℕ) < p + (n + 1) + 1
    omega

end SSet
