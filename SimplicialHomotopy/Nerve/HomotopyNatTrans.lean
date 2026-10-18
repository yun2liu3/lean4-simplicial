/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.WeakEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.SingleObj

/-!
# A simplicial homotopy between nerves is the nerve of a natural transformation

A natural transformation `β : F ⟶ G` gives a simplicial homotopy
`Homotopy (nerveMap F) (nerveMap G)` (that direction is not part of this library). This file
proves the converse, and draws the consequences for one-object targets:

* `SSet.natTransOfHomotopy H : F ⟶ G` — for `F G : J ⥤ E` and `H : Homotopy (nerveMap F)
  (nerveMap G)`, the natural transformation whose component at `a` is the edge of the
  1-simplex `H.h (s₀ a, (0,1))` of `nerve E` (`s₀ a` the degenerate edge at `a`), transported
  to `F.obj a ⟶ G.obj a` along the identifications `homotopyEdge_obj_zero/one` of its
  endpoints. The naturality is `natTransOfHomotopyApp_naturality`.
* `SSet.exists_conj_of_homotopy_nerveMap` — the one-object case: for `F G : J ⥤ SingleObj M`,
  `M` a monoid, there is `θ : J → M` (namely `conjOfHomotopy H`) with the naturality squares
  `F.map u ≫ θ b = θ a ≫ G.map u`, i.e. `θ b * F.map u = G.map u * θ a` in `M`.
* `SSet.map_eq_of_homotopy_const`, `SSet.map_eq_of_const_homotopy` — for `M` a group, a
  homotopy between `nerveMap F` and a constant map (in either direction) forces `F` to be
  constant on parallel arrows: `F.map u = F.map v`. (Commutativity is not needed: with
  `G = const`, `θ b * F.map u = θ a`.)

**The 2-simplex argument.** Write `h₁ = H.h.app (op ⦋1⦌)`, `h₂ = H.h.app (op ⦋2⦌)`,
`e = (0,1) ∈ Δ[1]₁`. For `u : a ⟶ b` the two nondegenerate 2-simplices of the prism
`nerve J ⊗ Δ[1]` over `u` are `s₁ = (σ₁ u, σ₀ e) = (u, 𝟙_b ; 0,0,1)` and
`s₂ = (σ₀ u, σ₁ e) = (𝟙_a, u ; 0,1,1)`. Naturality of `H.h` for the three face maps
(`Homotopy.δ_h_app`) identifies the faces of `h₂ s₁` with `F u`, `h₁ (u, e)`, `h₁ (s₀ b, e)`
and those of `h₂ s₂` with `h₁ (s₀ a, e)`, `h₁ (u, e)`, `G u`; the composition law
`ComposableArrows.map'_comp` of a 2-simplex (`edgeTo_δ_one`) then gives
`F.map u ≫ θ b = edge (h₁ (u, e)) = θ a ≫ G.map u`. All faces of `s₁`, `s₂` are computed from
the simplicial identities `δ_comp_σ_*_apply` (nerve factor) and `fin_cases`/`rfl` (`Δ[1]`
factor), so the only equalities of `ComposableArrows` needed are `ext₀` on vertices.

**Bookkeeping.** `SSet.edgeTo x h₀ h₁ : X ⟶ Y` is the edge of `x : N(E)₁` transported along
`h₀ : x.obj' 0 = X`, `h₁ : x.obj' 1 = Y`; it is transported along equalities of simplices by
`edgeTo_congr` (a `subst`), so no `eqToHom` computation is ever done by hand. Universes:
`nerveMap` needs `J E : Type u` with the same hom universe. `SingleObj M : Type` lives in
universe `0` whatever the universe of `M`, so the one-object statements have `J : Type` (with
`[Category.{u} J]` and `M : Type u` free); morphisms of `SingleObj M` are elements of `M`
definitionally, so `conjOfHomotopy H a : M` is literally `(natTransOfHomotopy H).app a`.
-/

universe u v

open CategoryTheory MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-- The nondegenerate edge `(0,1)` of `Δ[1]`, i.e. `𝟙 ⦋1⦌` under `stdSimplex.objEquiv`. -/
def edge₀₁ : (Δ[1] : SSet.{u}) _⦋1⦌ := stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-! ### Faces of the relevant simplices of the prism `nerve J ⊗ Δ[1]` -/

section Prism

variable {J : Type u} [Category.{v} J]

/-! The 1-simplex `(s₀ a, (0,1))` over a vertex `a`: its faces are `ι₀ a` and `ι₁ a`. -/

lemma prism_δ_one_vertex (a : J) :
    (nerve J ⊗ Δ[1]).δ 1 ((nerve J).σ 0 (ComposableArrows.mk₀ a), edge₀₁) =
      ι₀.app _ (ComposableArrows.mk₀ a) :=
  Prod.ext ((nerve J).δ_comp_σ_succ_apply 0 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

lemma prism_δ_zero_vertex (a : J) :
    (nerve J ⊗ Δ[1]).δ 0 ((nerve J).σ 0 (ComposableArrows.mk₀ a), edge₀₁) =
      ι₁.app _ (ComposableArrows.mk₀ a) :=
  Prod.ext ((nerve J).δ_comp_σ_self_apply 0 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

variable {a b : J} (u : a ⟶ b)

/-! Faces of the 2-simplex `s₁ = (σ₁ u, σ₀ e) = (u, 𝟙_b ; 0,0,1)`. -/

lemma prism_δ_zero_s₁ :
    (nerve J ⊗ Δ[1]).δ 0 ((nerve J).σ 1 (ComposableArrows.mk₁ u), Δ[1].σ 0 edge₀₁) =
      ((nerve J).σ 0 (ComposableArrows.mk₀ b), edge₀₁) :=
  Prod.ext
    (((nerve J).δ_comp_σ_of_le_apply (i := 0) (j := 0) (Fin.zero_le _) _).trans
      (congrArg _ (ComposableArrows.ext₀ rfl)))
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

lemma prism_δ_one_s₁ :
    (nerve J ⊗ Δ[1]).δ 1 ((nerve J).σ 1 (ComposableArrows.mk₁ u), Δ[1].σ 0 edge₀₁) =
      (ComposableArrows.mk₁ u, edge₀₁) :=
  Prod.ext ((nerve J).δ_comp_σ_self_apply 1 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

lemma prism_δ_two_s₁ :
    (nerve J ⊗ Δ[1]).δ 2 ((nerve J).σ 1 (ComposableArrows.mk₁ u), Δ[1].σ 0 edge₀₁) =
      ι₀.app _ (ComposableArrows.mk₁ u) :=
  Prod.ext ((nerve J).δ_comp_σ_succ_apply 1 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

/-! Faces of the 2-simplex `s₂ = (σ₀ u, σ₁ e) = (𝟙_a, u ; 0,1,1)`. -/

lemma prism_δ_zero_s₂ :
    (nerve J ⊗ Δ[1]).δ 0 ((nerve J).σ 0 (ComposableArrows.mk₁ u), Δ[1].σ 1 edge₀₁) =
      ι₁.app _ (ComposableArrows.mk₁ u) :=
  Prod.ext ((nerve J).δ_comp_σ_self_apply 0 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

lemma prism_δ_one_s₂ :
    (nerve J ⊗ Δ[1]).δ 1 ((nerve J).σ 0 (ComposableArrows.mk₁ u), Δ[1].σ 1 edge₀₁) =
      (ComposableArrows.mk₁ u, edge₀₁) :=
  Prod.ext ((nerve J).δ_comp_σ_succ_apply 0 _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

lemma prism_δ_two_s₂ :
    (nerve J ⊗ Δ[1]).δ 2 ((nerve J).σ 0 (ComposableArrows.mk₁ u), Δ[1].σ 1 edge₀₁) =
      ((nerve J).σ 0 (ComposableArrows.mk₀ a), edge₀₁) :=
  Prod.ext
    (((nerve J).δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) _).trans
      (congrArg _ (ComposableArrows.ext₀ rfl)))
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)

end Prism

/-! ### The edge of a 1-simplex of a nerve, with prescribed endpoints -/

section EdgeTo

variable {E : Type u} [Category.{v} E]

/-- The edge of `x : N(E)₁` as a morphism `X ⟶ Y`, along identifications of its endpoints. -/
def edgeTo (x : ComposableArrows E 1) {X Y : E} (h₀ : x.obj' 0 = X) (h₁ : x.obj' 1 = Y) :
    X ⟶ Y :=
  eqToHom h₀.symm ≫ x.map' 0 1 ≫ eqToHom h₁

lemma edgeTo_congr {x y : ComposableArrows E 1} (h : x = y) {X Y : E} (hx₀ : x.obj' 0 = X)
    (hx₁ : x.obj' 1 = Y) (hy₀ : y.obj' 0 = X) (hy₁ : y.obj' 1 = Y) :
    edgeTo x hx₀ hx₁ = edgeTo y hy₀ hy₁ := by
  subst h; rfl

/-- The composition law of a 2-simplex `z` of a nerve: its long edge `δ₁ z` is the composite
of the short edges `δ₂ z` and `δ₀ z`. -/
lemma edgeTo_δ_one (z : ComposableArrows E 2) {X Y Z : E} (h₀ : z.obj' 0 = X)
    (h₁ : z.obj' 1 = Y) (h₂ : z.obj' 2 = Z) :
    edgeTo ((nerve E).δ 1 z) h₀ h₂ =
      edgeTo ((nerve E).δ 2 z) h₀ h₁ ≫ edgeTo ((nerve E).δ 0 z) h₁ h₂ := by
  subst h₀ h₁ h₂
  show eqToHom rfl ≫ z.map' 0 2 ≫ eqToHom rfl =
    (eqToHom rfl ≫ z.map' 0 1 ≫ eqToHom rfl) ≫ (eqToHom rfl ≫ z.map' 1 2 ≫ eqToHom rfl)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact z.map'_comp 0 1 2

variable {J : Type u} [Category.{v} J] (F : J ⥤ E)

lemma edgeTo_nerveMap_mk₁ {a b : J} (u : a ⟶ b) :
    edgeTo ((nerveMap F).app (op ⦋1⦌) (ComposableArrows.mk₁ u)) rfl rfl = F.map u := by
  show eqToHom (rfl : F.obj a = F.obj a) ≫ F.map u ≫ eqToHom (rfl : F.obj b = F.obj b) = F.map u
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end EdgeTo

/-! ### Evaluating a homotopy on the ends of the cylinder and on faces -/

section Homotopy

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

lemma Homotopy.h_app_ι₀ (H : Homotopy f g) {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    H.h.app n (ι₀.app n x) = f.app n x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ n) x

lemma Homotopy.h_app_ι₁ (H : Homotopy f g) {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    H.h.app n (ι₁.app n x) = g.app n x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ n) x

/-- Naturality of `H.h` at a face `δ i`, followed by a computation `δ i s = t` of the face. -/
lemma Homotopy.δ_h_app (H : Homotopy f g) {n : ℕ} (i : Fin (n + 2)) (s : (X ⊗ Δ[1]) _⦋n + 1⦌)
    {t : (X ⊗ Δ[1]) _⦋n⦌} (ht : (X ⊗ Δ[1]).δ i s = t) :
    Y.δ i (H.h.app (op ⦋n + 1⦌) s) = H.h.app (op ⦋n⦌) t := by
  subst ht
  exact (δ_naturality_apply H.h i s).symm

end Homotopy

/-! ### The natural transformation extracted from a homotopy -/

section NatTrans

variable {J E : Type u} [Category.{v} J] [Category.{v} E] {F G : J ⥤ E}
  (H : Homotopy (nerveMap F) (nerveMap G))

/-- The 1-simplex `H.h (s₀ a, (0,1))` of `nerve E`, an edge from `F.obj a` to `G.obj a`. -/
def homotopyEdge (a : J) : ComposableArrows E 1 :=
  H.h.app (op ⦋1⦌) ((nerve J).σ 0 (ComposableArrows.mk₀ a), edge₀₁)

lemma homotopyEdge_obj_zero (a : J) : (homotopyEdge H a).obj' 0 = F.obj a :=
  congrArg (fun y : ComposableArrows E 0 ↦ y.obj' 0)
    ((H.δ_h_app 1 _ (prism_δ_one_vertex a)).trans (H.h_app_ι₀ _))

lemma homotopyEdge_obj_one (a : J) : (homotopyEdge H a).obj' 1 = G.obj a :=
  congrArg (fun y : ComposableArrows E 0 ↦ y.obj' 0)
    ((H.δ_h_app 0 _ (prism_δ_zero_vertex a)).trans (H.h_app_ι₁ _))

/-- The component at `a` of the natural transformation extracted from `H`: the edge of
`homotopyEdge H a`, transported to `F.obj a ⟶ G.obj a`. -/
def natTransOfHomotopyApp (a : J) : F.obj a ⟶ G.obj a :=
  edgeTo (homotopyEdge H a) (homotopyEdge_obj_zero H a) (homotopyEdge_obj_one H a)

/-- Naturality, by the 2-simplex argument (see the module docstring). -/
theorem natTransOfHomotopyApp_naturality {a b : J} (u : a ⟶ b) :
    F.map u ≫ natTransOfHomotopyApp H b = natTransOfHomotopyApp H a ≫ G.map u := by
  -- the common edge `c = H.h (u, (0,1))`
  set c : ComposableArrows E 1 := H.h.app (op ⦋1⦌) (ComposableArrows.mk₁ u, edge₀₁) with hc
  -- the 2-simplex `z = H.h (u, 𝟙_b ; 0,0,1)`, with faces `F u`, `c` and `homotopyEdge H b`
  set z : ComposableArrows E 2 :=
    H.h.app (op ⦋2⦌) ((nerve J).σ 1 (ComposableArrows.mk₁ u), Δ[1].σ 0 edge₀₁) with hz
  have f₂ : (nerve E).δ 2 z = (nerveMap F).app (op ⦋1⦌) (ComposableArrows.mk₁ u) :=
    (H.δ_h_app 2 _ (prism_δ_two_s₁ u)).trans (H.h_app_ι₀ _)
  have f₀ : (nerve E).δ 0 z = homotopyEdge H b := H.δ_h_app 0 _ (prism_δ_zero_s₁ u)
  have f₁ : (nerve E).δ 1 z = c := H.δ_h_app 1 _ (prism_δ_one_s₁ u)
  have z₀ : z.obj' 0 = F.obj a := congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 0) f₂
  have z₁ : z.obj' 1 = F.obj b := congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 1) f₂
  have z₂ : z.obj' 2 = G.obj b :=
    (congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 1) f₀).trans (homotopyEdge_obj_one H b)
  have c₀ : c.obj' 0 = F.obj a :=
    (congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 0) f₁).symm.trans z₀
  have c₁ : c.obj' 1 = G.obj b :=
    (congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 1) f₁).symm.trans z₂
  have k₁ : edgeTo c c₀ c₁ = F.map u ≫ natTransOfHomotopyApp H b :=
    (edgeTo_congr f₁.symm c₀ c₁ z₀ z₂).trans ((edgeTo_δ_one z z₀ z₁ z₂).trans
      (congrArg₂ (fun (p : F.obj a ⟶ F.obj b) (q : F.obj b ⟶ G.obj b) ↦ p ≫ q)
        ((edgeTo_congr f₂ z₀ z₁ rfl rfl).trans (edgeTo_nerveMap_mk₁ F u))
        (edgeTo_congr f₀ z₁ z₂ _ _)))
  -- the 2-simplex `w = H.h (𝟙_a, u ; 0,1,1)`, with faces `homotopyEdge H a`, `c` and `G u`
  set w : ComposableArrows E 2 :=
    H.h.app (op ⦋2⦌) ((nerve J).σ 0 (ComposableArrows.mk₁ u), Δ[1].σ 1 edge₀₁) with hw
  have g₂ : (nerve E).δ 2 w = homotopyEdge H a := H.δ_h_app 2 _ (prism_δ_two_s₂ u)
  have g₀ : (nerve E).δ 0 w = (nerveMap G).app (op ⦋1⦌) (ComposableArrows.mk₁ u) :=
    (H.δ_h_app 0 _ (prism_δ_zero_s₂ u)).trans (H.h_app_ι₁ _)
  have g₁ : (nerve E).δ 1 w = c := H.δ_h_app 1 _ (prism_δ_one_s₂ u)
  have w₀ : w.obj' 0 = F.obj a :=
    (congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 0) g₂).trans (homotopyEdge_obj_zero H a)
  have w₁ : w.obj' 1 = G.obj a := congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 0) g₀
  have w₂ : w.obj' 2 = G.obj b := congrArg (fun y : ComposableArrows E 1 ↦ y.obj' 1) g₀
  have k₂ : edgeTo c c₀ c₁ = natTransOfHomotopyApp H a ≫ G.map u :=
    (edgeTo_congr g₁.symm c₀ c₁ w₀ w₂).trans ((edgeTo_δ_one w w₀ w₁ w₂).trans
      (congrArg₂ (fun (p : F.obj a ⟶ G.obj a) (q : G.obj a ⟶ G.obj b) ↦ p ≫ q)
        (edgeTo_congr g₂ w₀ w₁ _ _)
        ((edgeTo_congr g₀ w₁ w₂ rfl rfl).trans (edgeTo_nerveMap_mk₁ G u))))
  exact k₁.symm.trans k₂

/-- **A simplicial homotopy between nerves is the nerve of a natural transformation.** From
`H : Homotopy (nerveMap F) (nerveMap G)` we extract `F ⟶ G`. -/
def natTransOfHomotopy : F ⟶ G where
  app := natTransOfHomotopyApp H
  naturality _ _ := natTransOfHomotopyApp_naturality H

@[simp]
lemma natTransOfHomotopy_app (a : J) :
    (natTransOfHomotopy H).app a = natTransOfHomotopyApp H a := rfl

end NatTrans

/-! ### The one-object case: a homotopy is a conjugation -/

section SingleObj

variable {M : Type u} [Monoid M] {J : Type} [Category.{u} J] {F G : J ⥤ SingleObj M}

/-- The conjugating element at `a` extracted from a homotopy `nerveMap F ⟶ nerveMap G`: the
component `(natTransOfHomotopy H).app a`, an element of `M`. -/
def conjOfHomotopy (H : Homotopy (nerveMap F) (nerveMap G)) (a : J) : M :=
  natTransOfHomotopyApp H a

/-- **A homotopy between nerves of functors into `SingleObj M` is a conjugation.** From
`H : Homotopy (nerveMap F) (nerveMap G)` we get `θ : J → M` (namely `conjOfHomotopy H`) with
`F.map u ≫ θ b = θ a ≫ G.map u`, i.e. `θ b * F.map u = G.map u * θ a` in `M`, for every
`u : a ⟶ b`. -/
theorem exists_conj_of_homotopy_nerveMap (H : Homotopy (nerveMap F) (nerveMap G)) :
    ∃ θ : J → M, ∀ {a b : J} (u : a ⟶ b),
      F.map u ≫ (θ b : F.obj b ⟶ G.obj b) = (θ a : F.obj a ⟶ G.obj a) ≫ G.map u :=
  ⟨conjOfHomotopy H, fun u ↦ natTransOfHomotopyApp_naturality H u⟩

end SingleObj

/-! ### Homotopic to a constant map: `F` is constant on parallel arrows -/

section Group

variable {M : Type u} [Group M] {J : Type} [Category.{u} J] {F : J ⥤ SingleObj M}

/-- `SSet.const k = nerveMap (const star)`
(`k = mk₀ star` by `ComposableArrows.ext₀`). -/
lemma const_eq_nerveMap_const (k : (nerve (SingleObj M)) _⦋0⦌) :
    (SSet.const k : nerve J ⟶ nerve (SingleObj M)) =
      nerveMap ((CategoryTheory.Functor.const J).obj (SingleObj.star M)) := by
  obtain rfl : k = ComposableArrows.mk₀ (SingleObj.star M) := ComposableArrows.ext₀ rfl
  rfl

/-- If `nerveMap F` is homotopic to a constant map (`M` a group) then `F` sends parallel arrows
to the same element: `F.map u = F.map v` (both equal `(θ b)⁻¹ * θ a` for the family `θ` of
`exists_conj_of_homotopy_nerveMap`). -/
theorem map_eq_of_homotopy_const (k : (nerve (SingleObj M)) _⦋0⦌)
    (H : Homotopy (nerveMap F) (SSet.const k)) {a b : J} (u v : a ⟶ b) :
    F.map u = F.map v := by
  obtain ⟨θ, hθ⟩ := exists_conj_of_homotopy_nerveMap (H.ofEq' rfl (const_eq_nerveMap_const k))
  have key : ∀ w : a ⟶ b, (F.map w : M) = (θ b)⁻¹ * θ a := fun w ↦ by
    have h : θ b * (F.map w : M) = 1 * θ a := hθ w
    exact eq_inv_mul_of_mul_eq (h.trans (one_mul _))
  exact (key u).trans (key v).symm

/-- The same with the homotopy in the other direction (both sides equal `θ b * (θ a)⁻¹`). -/
theorem map_eq_of_const_homotopy (k : (nerve (SingleObj M)) _⦋0⦌)
    (H : Homotopy (SSet.const k) (nerveMap F)) {a b : J} (u v : a ⟶ b) :
    F.map u = F.map v := by
  obtain ⟨θ, hθ⟩ := exists_conj_of_homotopy_nerveMap (H.ofEq' (const_eq_nerveMap_const k) rfl)
  have key : ∀ w : a ⟶ b, (F.map w : M) = θ b * (θ a)⁻¹ := fun w ↦ by
    have h : θ b * 1 = (F.map w : M) * θ a := hθ w
    exact eq_mul_inv_of_mul_eq ((mul_one _).symm.trans h).symm
  exact (key u).trans (key v).symm

end Group

end SSet
