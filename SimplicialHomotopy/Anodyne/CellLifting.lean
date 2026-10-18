/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.RightFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex

/-!
# Cellwise lifting along the filtration of a rank function

Let `A` be a subcomplex of a simplicial set `X`, `P : A.Pairing` a proper pairing and
`f : P.RankFunction ℕ` an `ℕ`-valued rank function. Mathlib
(`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex`) exhibits the
inclusion `A.ι : A ⟶ X` as the transfinite composition of the filtration `f.filtration j`,
each step `f.filtration j ⟶ f.filtration (j + 1)` being the pushout of a coproduct of horn
inclusions `c.horn.ι : Λ[c.dim + 1, c.index] ⟶ Δ[c.dim + 1]` indexed by the cells
`c : f.Cell j`.

This file proves the corresponding *conditional* lifting principle: a lifting problem
`(u : A ⟶ E, g : X ⟶ B)` against `q : E ⟶ B` has a solution as soon as every individual
cell's horn-extension problem can be solved *given the partial solution so far*. Unlike the
ordinary "left lifting properties are closed under transfinite composition" argument, the
hypothesis on a cell is allowed to depend on the partial lift `v : f.filtration j ⟶ E` already
constructed; this is what is needed when the cells attached along right horns are filled by a
right fibration while the cells attached along the outer horns `Λ[n + 1, 0]` need a
hypothesis on the partial lift.

* `SSet.Subcomplex.Pairing.RankFunction.PartialLift` : a lift on `f.filtration j`, compatible
  with `u` and `g`.
* `SSet.Subcomplex.Pairing.RankFunction.PartialLift.succ` : the successor step, by the pushout
  square `f.isPushout j`.
* `SSet.Subcomplex.Pairing.RankFunction.exists_lift` : the cellwise lifting principle.
* `SSet.Subcomplex.Pairing.RankFunction.exists_lift_of_rightFibration` : the same for a right
  fibration `q`, where only the outer-horn cells (`c.index = 0`) need a hypothesis.
* `SSet.Subcomplex.Pairing.RankFunction.Cell.exists_equivII`, `Cell.dim_eq`, `Cell.index_val`,
  `Cell.map_app` : for a pairing coming from a `PairingCore`, every cell is indexed by an
  element of the core, which gives its dimension, its horn index and its attaching map.
-/

universe u

open CategoryTheory Limits

open scoped Simplicial

namespace SSet.Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing} [P.IsProper] (f : P.RankFunction ℕ)

omit [P.IsProper] in
lemma filtration_zero : f.filtration 0 = A := f.filtration_bot

omit [P.IsProper] in
lemma filtration_le {j k : ℕ} (h : j ≤ k) : f.filtration j ≤ f.filtration k :=
  f.filtration_monotone h

omit [P.IsProper] in
lemma filtration_le_succ (j : ℕ) : f.filtration j ≤ f.filtration (j + 1) :=
  f.filtration_monotone (Nat.le_succ j)

omit [P.IsProper] in
lemma filtration_le_orderSucc (j : ℕ) : f.filtration j ≤ f.filtration (Order.succ j) :=
  f.filtration_monotone (Order.le_succ j)

/-- The pushout square `f.isPushout j`, restated with the inequality `f.filtration_le_orderSucc j`
(the term `f.filtration_monotone (Order.le_succ j)` is not type-correct at reducible
transparency, which prevents `rw` from matching goals which contain it). -/
lemma isPushout_orderSucc (j : ℕ) :
    IsPushout (f.t j) (f.m j) (Subcomplex.homOfLE (f.filtration_le_orderSucc j)) (f.b j) :=
  f.isPushout j

section

variable {E B : SSet.{u}} (q : E ⟶ B) (g : X ⟶ B) (u : (A : SSet.{u}) ⟶ E)

/-- A partial solution of the lifting problem `(u, g)` against `q`, defined on the
`j`-th step `f.filtration j` of the filtration. -/
structure PartialLift (j : ℕ) where
  /-- the partial lift -/
  v : (f.filtration j : SSet.{u}) ⟶ E
  v_q : v ≫ q = (f.filtration j).ι ≫ g
  homOfLE_v : Subcomplex.homOfLE (f.le_filtration j) ≫ v = u

namespace PartialLift

variable {f q g u}

/-- The partial lift on `f.filtration 0 = A` given by `u`. -/
def zero (hu : u ≫ q = A.ι ≫ g) : f.PartialLift q g u 0 where
  v := Subcomplex.homOfLE (f.filtration_zero).le ≫ u
  v_q := by rw [Category.assoc, hu, Subcomplex.homOfLE_ι_assoc]
  homOfLE_v := by
    rw [← Category.assoc, Subcomplex.homOfLE_comp, Subcomplex.homOfLE_refl, Category.id_comp]

section succ

variable {j : ℕ} (p : f.PartialLift q g u j)
  (H : ∀ c : f.Cell j, ∃ w : Δ[c.dim + 1] ⟶ E,
    c.horn.ι ≫ w = c.mapHorn ≫ p.v ∧ w ≫ q = c.map ≫ g)

/-- The chosen extensions over the cells of rank `j`, assembled on `f.sigmaStdSimplex j`. -/
noncomputable def sigmaExtension : f.sigmaStdSimplex j ⟶ E :=
  Sigma.desc fun c ↦ (H c).choose

@[reassoc (attr := simp)]
lemma ι_sigmaExtension (c : f.Cell j) :
    c.ιSigmaStdSimplex ≫ p.sigmaExtension H = (H c).choose :=
  Sigma.ι_desc _ _

lemma t_comp_v : f.t j ≫ p.v = f.m j ≫ p.sigmaExtension H := by
  ext c : 1
  rw [Cell.ι_t_assoc, Cell.ι_m_assoc, ι_sigmaExtension, (H c).choose_spec.1]

/-- The successor step: extend a partial lift on `f.filtration j` to
`f.filtration (Order.succ j)` (which is `f.filtration (j + 1)`) using the pushout square
`f.isPushout j` and the chosen cell extensions. -/
noncomputable def succ : f.PartialLift q g u (Order.succ j) where
  v := (f.isPushout_orderSucc j).desc p.v (p.sigmaExtension H) (p.t_comp_v H)
  v_q := by
    apply (f.isPushout_orderSucc j).hom_ext
    · rw [IsPushout.inl_desc_assoc, p.v_q, Subcomplex.homOfLE_ι_assoc]
    · rw [IsPushout.inr_desc_assoc]
      ext c : 1
      rw [ι_sigmaExtension_assoc, (H c).choose_spec.2, Cell.ι_b_assoc, Cell.mapToSucc_ι_assoc]
  homOfLE_v := by
    rw [← Subcomplex.homOfLE_comp (f.le_filtration j) (f.filtration_le_orderSucc j),
      Category.assoc, IsPushout.inl_desc, p.homOfLE_v]

@[reassoc (attr := simp)]
lemma homOfLE_succ_v :
    Subcomplex.homOfLE (f.filtration_le_orderSucc j) ≫ (p.succ H).v = p.v :=
  (f.isPushout_orderSucc j).inl_desc _ _ _

end succ

end PartialLift

variable (hu : u ≫ q = A.ι ≫ g)
  (H : ∀ (j : ℕ) (c : f.Cell j) (v : (f.filtration j : SSet.{u}) ⟶ E),
    v ≫ q = (f.filtration j).ι ≫ g → Subcomplex.homOfLE (f.le_filtration j) ≫ v = u →
    ∃ w : Δ[c.dim + 1] ⟶ E, c.horn.ι ≫ w = c.mapHorn ≫ v ∧ w ≫ q = c.map ≫ g)

/-- The sequence of partial lifts obtained by iterating `PartialLift.succ`. -/
noncomputable def partialLift : ∀ j : ℕ, f.PartialLift q g u j
  | 0 => PartialLift.zero hu
  | j + 1 => (partialLift j).succ (fun c ↦ H j c _ (partialLift j).v_q (partialLift j).homOfLE_v)

@[reassoc (attr := simp)]
lemma homOfLE_partialLift_succ_v (j : ℕ) :
    Subcomplex.homOfLE (f.filtration_le_succ j) ≫ (f.partialLift q g u hu H (j + 1)).v =
      (f.partialLift q g u hu H j).v :=
  PartialLift.homOfLE_succ_v _ _

lemma homOfLE_partialLift_v {j k : ℕ} (h : j ≤ k) :
    Subcomplex.homOfLE (f.filtration_le h) ≫ (f.partialLift q g u hu H k).v =
      (f.partialLift q g u hu H j).v := by
  induction k, h using Nat.le_induction with
  | base => rw [Subcomplex.homOfLE_refl, Category.id_comp]
  | succ k hjk ih =>
    rw [← Subcomplex.homOfLE_comp (f.filtration_le hjk) (f.filtration_le_succ k),
      Category.assoc, homOfLE_partialLift_succ_v, ih]

/-- The partial lifts assemble into a cocone on the filtration with point `E`. -/
@[simps]
noncomputable def partialLiftCocone :
    Cocone (f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor) where
  pt := E
  ι :=
    { app := fun j ↦ (f.partialLift q g u hu H j).v
      naturality := fun j k h ↦ by
        simp only [Functor.const_obj_map]
        exact f.homOfLE_partialLift_v q g u hu H (leOfHom h) }

/-- The colimit cocone of the filtration, with point `(⊤ : X.Subcomplex)`. -/
noncomputable def filtrationCocone :
    Cocone (f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor) :=
  Subcomplex.toSSetFunctor.mapCocone
    (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
      (by rw [← f.iSup_filtration]; apply isLUB_iSup)).cocone

lemma filtrationCocone_pt : (f.filtrationCocone).pt = ((⊤ : X.Subcomplex) : SSet.{u}) := rfl

lemma filtrationCocone_ι_app (j : ℕ) :
    (f.filtrationCocone).ι.app j = Subcomplex.homOfLE (le_top : f.filtration j ≤ ⊤) := rfl

/-- `f.filtrationCocone` is a colimit cocone. -/
noncomputable def isColimitFiltrationCocone : IsColimit f.filtrationCocone :=
  isColimitOfPreserves Subcomplex.toSSetFunctor
    (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
      (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit

omit [P.IsProper] in
lemma ι_topIso_inv (j : ℕ) :
    (f.filtration j).ι ≫ (Subcomplex.topIso X).inv =
      Subcomplex.homOfLE (le_top : f.filtration j ≤ ⊤) := by
  rw [← cancel_mono (Subcomplex.topIso X).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]

/-- Cellwise lifting principle along the filtration of an `ℕ`-valued rank function. -/
theorem exists_lift {E B : SSet.{u}} (q : E ⟶ B) (g : X ⟶ B) (u : (A : SSet.{u}) ⟶ E)
    (hu : u ≫ q = A.ι ≫ g)
    (H : ∀ (j : ℕ) (c : f.Cell j) (v : (f.filtration j : SSet.{u}) ⟶ E),
      v ≫ q = (f.filtration j).ι ≫ g → Subcomplex.homOfLE (f.le_filtration j) ≫ v = u →
      ∃ w : Δ[c.dim + 1] ⟶ E, c.horn.ι ≫ w = c.mapHorn ≫ v ∧ w ≫ q = c.map ≫ g) :
    ∃ l : X ⟶ E, A.ι ≫ l = u ∧ l ≫ q = g := by
  let hc := f.isColimitFiltrationCocone
  let d : ((⊤ : X.Subcomplex) : SSet.{u}) ⟶ E := hc.desc (f.partialLiftCocone q g u hu H)
  have hfac : ∀ j, Subcomplex.homOfLE (le_top : f.filtration j ≤ ⊤) ≫ d =
      (f.partialLift q g u hu H j).v := fun j ↦ hc.fac _ j
  refine ⟨(Subcomplex.topIso X).inv ≫ d, ?_, ?_⟩
  · rw [← Subcomplex.homOfLE_ι (f.le_filtration 0), Category.assoc, ← Category.assoc _ _ d,
      f.ι_topIso_inv, hfac, (f.partialLift q g u hu H 0).homOfLE_v]
  · rw [← cancel_epi (Subcomplex.topIso X).hom, Category.assoc, Iso.hom_inv_id_assoc,
      Subcomplex.topIso_hom]
    apply hc.hom_ext
    intro j
    have : Subcomplex.homOfLE (le_top : f.filtration j ≤ ⊤) ≫ d ≫ q =
        Subcomplex.homOfLE (le_top : f.filtration j ≤ ⊤) ≫ (⊤ : X.Subcomplex).ι ≫ g := by
      rw [← Category.assoc, hfac, (f.partialLift q g u hu H j).v_q, Subcomplex.homOfLE_ι_assoc]
    exact this

end

/-- The same, for a right fibration `q`: cells attached along right horns (`c.index ≠ 0`) are
filled automatically, only the outer-horn cells (`c.index = 0`) need a hypothesis. -/
theorem exists_lift_of_rightFibration {E B : SSet.{u}} (q : E ⟶ B) [RightFibration q]
    (g : X ⟶ B) (u : (A : SSet.{u}) ⟶ E) (hu : u ≫ q = A.ι ≫ g)
    (H₀ : ∀ (j : ℕ) (c : f.Cell j) (v : (f.filtration j : SSet.{u}) ⟶ E),
      v ≫ q = (f.filtration j).ι ≫ g → Subcomplex.homOfLE (f.le_filtration j) ≫ v = u →
      c.index = 0 →
      ∃ w : Δ[c.dim + 1] ⟶ E, c.horn.ι ≫ w = c.mapHorn ≫ v ∧ w ≫ q = c.map ≫ g) :
    ∃ l : X ⟶ E, A.ι ≫ l = u ∧ l ≫ q = g := by
  refine f.exists_lift q g u hu (fun j c v hv hvu ↦ ?_)
  by_cases h0 : c.index = 0
  · exact H₀ j c v hv hvu h0
  · have hn : 0 < c.index := (Fin.pos_iff_ne_zero' c.index).2 h0
    have : HasLiftingProperty c.horn.ι q :=
      (mem_rightFibrations q) _ (horn_ι_mem_rightHornInclusions hn)
    have sq : CommSq (c.mapHorn ≫ v) c.horn.ι q (c.map ≫ g) :=
      ⟨by rw [Category.assoc, hv, Cell.mapHorn_ι_assoc]⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SSet.Subcomplex.Pairing.RankFunction

/-! ### Cells of the pairing of a pairing core -/

namespace SSet

/-- Casting equal simplices to the same dimension gives the same simplex. -/
lemma S.cast_simplex_congr {X : SSet.{u}} {y y' : X.S} (h : y = y') {d : ℕ}
    (hd : y.dim = d) (hd' : y'.dim = d) :
    (y.cast hd).simplex = (y'.cast hd').simplex := by
  subst h; rfl

/-- The index of a uniquely codimension-one face only depends on the pair of simplices. -/
lemma S.IsUniquelyCodimOneFace.index_val_congr {X : SSet.{u}} {x y x' y' : X.S}
    (hxy : SSet.S.IsUniquelyCodimOneFace x y) (hxy' : SSet.S.IsUniquelyCodimOneFace x' y')
    (hx : x = x') (hy : y = y') {d : ℕ} (hd : x.dim = d) (hd' : x'.dim = d) :
    (hxy.index hd).val = (hxy'.index hd').val := by
  subst hx hy; rfl

namespace Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {h : A.PairingCore}
  {ι : Type*} [LinearOrder ι] {f : h.pairing.RankFunction ι} {j : ι}

/-- Every cell of the rank function of a pairing coming from a `PairingCore` is indexed by an
element of the core. -/
lemma Cell.exists_equivII (c : f.Cell j) : ∃ s : h.ι, c.s = h.equivII s := by
  obtain ⟨⟨x, s, rfl⟩, hc⟩ := c
  exact ⟨s, rfl⟩

/-- The dimension of a cell indexed by `s` is the dimension `h.dim s` of the core. -/
lemma Cell.dim_eq (c : f.Cell j) (s : h.ι) (hs : c.s = h.equivII s) :
    c.dim = h.dim s := by
  obtain ⟨t, hc⟩ := c
  dsimp only at hs
  subst hs
  rfl

variable [h.IsProper]

/-- The horn index of a cell indexed by `s` is the index `h.index s` of the core. -/
lemma Cell.index_val (c : f.Cell j) (s : h.ι) (hs : c.s = h.equivII s) :
    (c.index : ℕ) = h.index s := by
  obtain ⟨t, hc⟩ := c
  dsimp only at hs
  subst hs
  exact (S.IsUniquelyCodimOneFace.index_val_congr _ (h.isUniquelyCodimOneFace s) rfl
    (by rw [PairingCore.pairing_p_equivII]; rfl) rfl rfl).trans
    (h.isUniquelyCodimOneFace_index_coe s rfl)

/-- The attaching map of a cell indexed by `s` is the type (I) simplex `h.simplex s`. -/
lemma Cell.map_app (c : f.Cell j) (s : h.ι) (hs : c.s = h.equivII s)
    {k : ℕ} (y : Δ[c.dim + 1] _⦋k⦌) :
    c.map.app _ y = X.map (stdSimplex.objEquiv y).op
      (_root_.cast (by rw [c.dim_eq s hs]) (h.simplex s)) := by
  obtain ⟨t, hc⟩ := c
  dsimp only at hs
  subst hs
  have e : ((h.pairing.p (h.equivII s)).val.cast
      (h.pairing.isUniquelyCodimOneFace (h.equivII s)).dim_eq).simplex =
      _root_.cast (by rfl) (h.simplex s) :=
    S.cast_simplex_congr (y' := (h.type₁ s).toS) (by rw [PairingCore.pairing_p_equivII]; rfl)
      (h.pairing.isUniquelyCodimOneFace (h.equivII s)).dim_eq rfl
  exact congrArg (X.map (stdSimplex.objEquiv y).op) e

end Subcomplex.Pairing.RankFunction

end SSet
