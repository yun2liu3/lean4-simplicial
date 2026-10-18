/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Nerve.NerveHo
import SimplicialHomotopy.Equivalence.KanOfEquiv
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory

/-!
# Equivalences in a quasicategory versus isomorphisms in `hC`; `toNerveHo C` is an isofibration

* `SSet.Edge.IsEquiv e` (from `KanOfEquiv.lean`): an edge is an *equivalence* if it admits an
  `InvStruct`
  (an inverse edge together with two `2`-simplices witnessing the two composition identities).
* `SimplicialHomotopy.isIso_homMk_of_isEquiv` : an equivalence becomes an isomorphism in the
  homotopy category.
* `SimplicialHomotopy.exists_edge_homMk_eq` : in a quasicategory, every morphism of the homotopy
  category is `homMk` of a single edge (inner horn filling `Λ[2,1]`).
* `SimplicialHomotopy.isEquiv_of_isIso_homMk` : conversely, an edge of a quasicategory which
  becomes an isomorphism in `hC` is an equivalence (via the comparison functor
  `SimplicialHomotopy.toHomotopyCategory₂ : C.HomotopyCategory ⥤ HomotopyCategory₂ (truncation 2 C)`
  and Mathlib's `Edge.CompStruct.ofHomotopyCategory₂Fac`).
* `SimplicialHomotopy.Isofibration F` for `F : C ⟶ nerve A` : for every vertex
  `c` and every isomorphism `u : F(c) ≅ y` in `A`, there is an equivalence `e' : c → y'` in `C`
  with `F(e') = u`.
* `SimplicialHomotopy.isofibration_toNerveHo` : `C ⟶ N(hC)` is an
  isofibration when `C` is a quasicategory.
* `SimplicialHomotopy.isofibration_to_nerve_partialOrder` : every map
  `C ⟶ N P` to the nerve of a poset is an isofibration, since the only isomorphisms of a poset
  are identities.
-/

universe u

open CategoryTheory Simplicial SSet SSet.HomotopyCategory

namespace SimplicialHomotopy

/-! Equivalences of edges: `SSet.Edge.IsEquiv` (`KanOfEquiv.lean`). -/

/-! ### Equivalences become isomorphisms in the homotopy category -/

section IsIso

variable {C : SSet.{u}} {x y : C _⦋0⦌}

/-- An equivalence becomes an isomorphism in the homotopy category. -/
lemma isIso_homMk_of_isEquiv {e : C.Edge x y} (he : Edge.IsEquiv e) : IsIso (homMk e) := by
  obtain ⟨I⟩ := he
  exact ⟨homMk I.inv, by rw [homMk_comp_homMk I.homInvId, homMk_id],
    by rw [homMk_comp_homMk I.invHomId, homMk_id]⟩

/-- The inverse in `hC` of an equivalence is represented by the inverse edge. -/
lemma inv_homMk_of_invStruct {e : C.Edge x y} (I : e.InvStruct) :
    haveI := isIso_homMk_of_isEquiv ⟨I⟩
    inv (homMk e) = homMk I.inv := by
  have := isIso_homMk_of_isEquiv ⟨I⟩
  apply IsIso.inv_eq_of_hom_inv_id
  rw [homMk_comp_homMk I.homInvId, homMk_id]

end IsIso

/-! ### Every morphism of `hC` is represented by a single edge -/

section Quasicategory

variable {C : SSet.{u}} [Quasicategory C]

/-- In a quasicategory, every morphism of the homotopy category is `homMk` of a single edge
(general form, for arbitrary objects of `hC`). -/
lemma exists_edge_objEquiv_homMk_eq {x y : C.HomotopyCategory} (φ : x ⟶ y) :
    ∃ e : C.Edge (objEquiv x) (objEquiv y), homMk e = φ := by
  induction φ using hom_rec with
  | homMk e => exact ⟨e, rfl⟩
  | comp f g hf hg =>
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨e', rfl⟩ := hg
    obtain ⟨e'', h⟩ := Truncated.Quasicategory₂.fill21 e.toTruncated e'.toTruncated
    exact ⟨SSet.Edge.ofTruncated e'', (homMk_comp_homMk (SSet.Edge.CompStruct.ofTruncated h)).symm⟩

/-- In a quasicategory, every morphism `mk x ⟶ mk y` of the homotopy category is `homMk e` for
some edge `e : x → y`. -/
lemma exists_edge_homMk_eq {x y : C _⦋0⦌} (φ : mk x ⟶ mk y) :
    ∃ e : C.Edge x y, homMk e = φ :=
  exists_edge_objEquiv_homMk_eq φ

/-! ### Comparison with `HomotopyCategory₂` and the converse -/

/-- The comparison functor from `hC` (the quotient of the free category on the underlying
reflexive quiver by the `2`-simplex relations) to Mathlib's `HomotopyCategory₂` (whose morphisms
are homotopy classes of edges), for a quasicategory `C`. On `homMk e` it is the class of `e`. -/
noncomputable def toHomotopyCategory₂ (C : SSet.{u}) [Quasicategory C] :
    C.HomotopyCategory ⥤ Truncated.HomotopyCategory₂ ((truncation 2).obj C) :=
  Truncated.HomotopyCategory.lift (fun x ↦ ⟨x⟩) (fun e ↦ Truncated.HomotopyCategory₂.homMk e)
    (fun _ ↦ rfl) (fun h ↦ h.homotopyCategory₂_fac)

@[simp]
lemma toHomotopyCategory₂_map_homMk (C : SSet.{u}) [Quasicategory C] {x y : C _⦋0⦌}
    (e : C.Edge x y) :
    (toHomotopyCategory₂ C).map (homMk e) = Truncated.HomotopyCategory₂.homMk e.toTruncated := by
  dsimp only [toHomotopyCategory₂]
  exact Truncated.HomotopyCategory.lift_map_homMk (map_comp := fun h ↦ h.homotopyCategory₂_fac)
    (map_id := fun _ ↦ rfl) _ _ e.toTruncated

/-- In a quasicategory, a relation `homMk e ≫ homMk e' = homMk e''` in the homotopy category is
witnessed by an actual `2`-simplex. -/
lemma nonempty_compStruct_of_homMk_comp_homMk_eq {x y z : C _⦋0⦌} {e : C.Edge x y}
    {e' : C.Edge y z} {e'' : C.Edge x z} (h : homMk e ≫ homMk e' = homMk e'') :
    Nonempty (SSet.Edge.CompStruct e e' e'') := by
  have h' := congrArg (toHomotopyCategory₂ C).map h
  rw [Functor.map_comp, toHomotopyCategory₂_map_homMk, toHomotopyCategory₂_map_homMk,
    toHomotopyCategory₂_map_homMk] at h'
  exact ⟨SSet.Edge.CompStruct.ofTruncated (.ofHomotopyCategory₂Fac h')⟩

/-- **Isomorphisms in `hC` are represented by equivalences.** An edge of a quasicategory which
becomes an isomorphism in the homotopy category is an equivalence. -/
lemma isEquiv_of_isIso_homMk {x y : C _⦋0⦌} (e : C.Edge x y) [IsIso (homMk e)] :
    Edge.IsEquiv e := by
  obtain ⟨e', he'⟩ := exists_edge_homMk_eq (inv (homMk e))
  obtain ⟨s₁⟩ := nonempty_compStruct_of_homMk_comp_homMk_eq (e := e) (e' := e')
    (e'' := SSet.Edge.id x) (by rw [he', IsIso.hom_inv_id, homMk_id])
  obtain ⟨s₂⟩ := nonempty_compStruct_of_homMk_comp_homMk_eq (e := e') (e' := e)
    (e'' := SSet.Edge.id y) (by rw [he', IsIso.inv_hom_id, homMk_id])
  exact ⟨{ inv := e', homInvId := s₁, invHomId := s₂ }⟩

/-- In a quasicategory, an edge is an equivalence iff it becomes an isomorphism in `hC`. -/
lemma isEquiv_iff_isIso_homMk {x y : C _⦋0⦌} (e : C.Edge x y) :
    Edge.IsEquiv e ↔ IsIso (homMk e) :=
  ⟨isIso_homMk_of_isEquiv, fun _ ↦ isEquiv_of_isIso_homMk e⟩

end Quasicategory

/-! ### Isofibrations -/

section Isofibration

variable {C : SSet.{u}} {A : Type u} [Category.{u} A]

/-- A map `F : C ⟶ N(A)` from a simplicial set to the nerve of a
category is an *isofibration* if for every vertex `c` of `C` and every isomorphism
`u : F(c) ≅ y` in `A`, there is an equivalence `e' : c → y'` in `C` with `F(e') = u`
(the equation being stated after identifying `F(y')` with `y`). -/
def Isofibration (F : C ⟶ nerve A) : Prop :=
  ∀ (c : C _⦋0⦌) (y : A) (u : nerveEquiv (F.app _ c) ≅ y),
    ∃ (y' : C _⦋0⦌) (e' : C.Edge c y'), Edge.IsEquiv e' ∧
      ∃ h : nerveEquiv (F.app _ y') = y, nerve.homEquiv (e'.map F) ≫ eqToHom h = u.hom

end Isofibration

section ToNerveHo

variable (C : SSet.{u})

/-- On vertices, `nerveEquiv ∘ toNerveHo C` is `HomotopyCategory.mk`. -/
lemma nerveEquiv_toNerveHo_app_zero (x : C _⦋0⦌) :
    nerveEquiv ((toNerveHo C).app _ x) = mk x := by
  rw [toNerveHo_app_zero]
  exact Equiv.apply_symm_apply _ _

/-- `nerve.homEquiv (e.map (toNerveHo C))` is `homMk e`, up to the identifications
`nerveEquiv_toNerveHo_app_zero` of the endpoints. -/
lemma homEquiv_edge_map_toNerveHo {x y : C _⦋0⦌} (e : C.Edge x y) :
    eqToHom (nerveEquiv_toNerveHo_app_zero C x).symm ≫ nerve.homEquiv (e.map (toNerveHo C)) ≫
      eqToHom (nerveEquiv_toNerveHo_app_zero C y) = homMk e := by
  have h := homEquiv_toNerveHo_edge C e
  have h' := nerve_homEquiv_ofEq (e.map (toNerveHo C)) (toNerveHo_app_zero C x)
    (toNerveHo_app_zero C y)
  exact h'.symm.trans h

/-- The canonical functor `C ⟶ N(hC)` of a quasicategory is an
isofibration: isomorphisms of `hC` are represented by equivalences of `C`. -/
theorem isofibration_toNerveHo [Quasicategory C] : Isofibration (toNerveHo C) := by
  intro c y u
  induction y using HomotopyCategory.rec with
  | mk y' =>
  obtain ⟨e, he⟩ := exists_edge_homMk_eq (eqToHom (nerveEquiv_toNerveHo_app_zero C c).symm ≫ u.hom)
  have : IsIso (homMk e) := by rw [he]; infer_instance
  refine ⟨y', e, isEquiv_of_isIso_homMk e, nerveEquiv_toNerveHo_app_zero C y', ?_⟩
  have key := homEquiv_edge_map_toNerveHo C e
  rw [he] at key
  exact (cancel_epi _).1 key

end ToNerveHo

/-! ### Maps to the nerve of a poset -/

section PartialOrder

/-- Every map from a simplicial set to the nerve of a poset is an isofibration: the only
isomorphisms of a poset are identities. -/
theorem isofibration_to_nerve_partialOrder {C : SSet.{u}} {P : Type u} [PartialOrder P]
    (F : C ⟶ nerve P) : Isofibration F := by
  intro c y u
  obtain rfl := u.to_eq
  exact ⟨c, SSet.Edge.id c, Edge.IsEquiv.id c, rfl, Subsingleton.elim _ _⟩

end PartialOrder

end SimplicialHomotopy
