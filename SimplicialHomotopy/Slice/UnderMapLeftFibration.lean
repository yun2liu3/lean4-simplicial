/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.Cone
import SimplicialHomotopy.Fibration.LeftFibrations

/-!
# `X_{c/} ⟶ Y_{F c/}` is a trivial fibration when `F` is a left fibration

This is [Lur09, Proposition 2.1.2.5] in its non-relative form: for a left fibration
`F : X ⟶ Y` and a vertex `c` of `X`, the induced map of undercategories
`underMap F c : X_{c/} ⟶ Y_{F c/}` has the right lifting property against all monomorphisms.

The proof transposes a lifting problem for `∂Δ[n] ↪ Δ[n]` against `underMap F c` across the
universal property of the cone (`SSet.coneHomEquiv`) into a lifting problem for
`Δ[0] ⋆ ∂Δ[n] ↪ Δ[0] ⋆ Δ[n]` against `F`, and under `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`
(`SSet.stdSimplex.coneIso`) the subcomplex `Δ[0] ⋆ ∂Δ[n]` is exactly the left horn
`Λ[n + 1, 0]`, against whose inclusion a left fibration has the right lifting property.

* `SSet.cone_boundary_eq_preimage_horn` : `Δ[0] ⋆ ∂Δ[n]` is the preimage of `Λ[n + 1, 0]`
  under `stdSimplex.coneIso n`.
* `SSet.hasLiftingProperty_cone_boundary_ι` : a left fibration has the right lifting property
  against `(Δ[0] ⋆ ∂Δ[n]) ↪ Δ[0] ⋆ Δ[n]`.
* `SSet.coneLift_toCone_comp`, `SSet.exists_lift_underMap_of_cone` : the transposition, for any
  subcomplex `B₀ ⊆ B`: a square against `underMap F c` gives a square against `F` on cones,
  and a solution of the latter gives a solution of the former.
* `SSet.hasLiftingProperty_boundary_underMap` : the transfer of that lifting property to
  `∂Δ[n].ι` against `underMap F c`.
* `SSet.rlp_monomorphisms_underMap_of_leftFibration` : the main theorem.
-/

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-! ### `Δ[0] ⋆ ∂Δ[n]` is the left horn `Λ[n + 1, 0]` -/

open stdSimplex in
/-- Under `stdSimplex.coneIso n : Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, which carries the cone point to the
vertex `0` and `coneι` to `δ 0`, the subcomplex `Δ[0] ⋆ ∂Δ[n]` of `Δ[0] ⋆ Δ[n]` is the preimage
of the left horn `Λ[n + 1, 0]`: a simplex of `Δ[n + 1]` misses a vertex other than `0` iff its
part in `{1, …, n + 1}` misses a vertex, i.e. iff its residual simplex lies in `∂Δ[n]`. -/
lemma cone_boundary_eq_preimage_horn (n : ℕ) :
    Subcomplex.cone (boundary.{u} n) = Λ[n + 1, 0].preimage (stdSimplex.coneIso.{u} n).hom := by
  ext m x
  obtain ⟨⟨p⟩⟩ := m
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    show (ConcreteCategory.hom ((coneIso.{u} n).hom.app (op ⦋p⦌))) x
        = objMk ((coneAug n x.y).comp (collapse x.j x.k x.hjk)) from
      toConeFun_toUnderVertex₀ _ _,
    mem_horn_iff_notMem_range, Subcomplex.mem_cone_iff]
  obtain ⟨j, k, hjk, y⟩ := x
  dsimp only at hjk ⊢
  rw [show Set.range
      ⇑(objMk ((coneAug n y).comp (collapse j k hjk)) : Δ[n + 1] _⦋p⦌) =
      Set.range (fun t ↦ coneAug n y (collapse j k hjk t)) from rfl]
  cases k with
  | zero =>
    -- the cone point: in `Δ[0] ⋆ ∂Δ[n]` trivially, and in the horn since it misses `1`
    refine iff_of_true trivial ⟨Fin.succ 0, Fin.succ_ne_zero 0, ?_⟩
    rintro ⟨t, ht⟩
    exact Fin.succ_ne_zero 0 ht.symm
  | succ k' =>
    have hzero : coneAug n y 0 = 0 := (coneAug_eq_zero_iff _ y 0).2 rfl
    have hsucc : ∀ t : Fin (k' + 1), coneAug n y t.succ = (asOrderHom y t).succ :=
      fun _ ↦ rfl
    refine Iff.trans (mem_boundary_iff_notMem_range (n := n) (d := k') y) ?_
    constructor
    · rintro ⟨v, hvr⟩
      refine ⟨v.succ, Fin.succ_ne_zero v, ?_⟩
      rintro ⟨t, ht⟩
      dsimp only at ht
      rcases Fin.eq_zero_or_eq_succ (collapse j (k' + 1) hjk t) with h | ⟨s, h⟩
      · rw [h, hzero] at ht
        exact Fin.succ_ne_zero v ht.symm
      · rw [h, hsucc] at ht
        exact hvr ⟨s, Fin.succ_inj.1 ht⟩
    · rintro ⟨w, hw, hwr⟩
      obtain ⟨v, rfl⟩ := Fin.eq_succ_of_ne_zero hw
      refine ⟨v, ?_⟩
      rintro ⟨t, ht⟩
      have htlt : (t : ℕ) + j < p + 1 := by have := t.isLt; omega
      refine hwr ⟨⟨(t : ℕ) + j, htlt⟩, ?_⟩
      have hc : collapse j (k' + 1) hjk ⟨(t : ℕ) + j, htlt⟩ = t.succ := by
        rw [Fin.ext_iff, collapse_apply_val]
        simp only [Fin.val_succ]
        omega
      dsimp only
      rw [hc, hsucc]
      exact congrArg Fin.succ ht

/-- A left fibration has the right lifting property against
`(Δ[0] ⋆ ∂Δ[n]) ↪ Δ[0] ⋆ Δ[n]`, this being the left horn inclusion `Λ[n + 1, 0] ↪ Δ[n + 1]`
transported along `stdSimplex.coneIso n`. -/
lemma hasLiftingProperty_cone_boundary_ι {X Y : SSet.{u}} (F : X ⟶ Y) [LeftFibration F]
    (n : ℕ) : HasLiftingProperty (Subcomplex.cone (boundary.{u} n)).ι F := by
  rw [cone_boundary_eq_preimage_horn n]
  have : HasLiftingProperty Λ[n + 1, 0].ι F :=
    mem_leftFibrations F _ (horn_ι_mem_leftHornInclusions (n := n + 1) (i := 0) Fin.last_pos)
  have e : Arrow.mk (Λ[n + 1, 0].preimage (stdSimplex.coneIso.{u} n).hom).ι ≅
      Arrow.mk Λ[n + 1, 0].ι :=
    Arrow.isoMk (Subcomplex.preimageIso Λ[n + 1, 0] (stdSimplex.coneIso n))
      (stdSimplex.coneIso n) rfl
  exact HasLiftingProperty.of_arrow_iso_left e.symm F

/-! ### The transfer across the cone -/

/-- A commutative square against `underMap F c` transposes, across the universal property
`coneHomEquiv` of the cone, to a commutative square against `F` on cones. -/
lemma coneLift_toCone_comp {X Y B : SSet.{u}} (F : X ⟶ Y) (c : X _⦋0⦌) (B₀ : B.Subcomplex)
    (a : (B₀ : SSet.{u}) ⟶ (X.under c : SSet.{u})) (b : B ⟶ (Y.under (F.app _ c) : SSet.{u}))
    (w : a ≫ underMap F c = B₀.ι ≫ b) :
    (Subcomplex.coneLift B₀ ≫ toCone a) ≫ F = (Subcomplex.cone B₀).ι ≫ toCone b := by
  calc (Subcomplex.coneLift B₀ ≫ toCone a) ≫ F
      = Subcomplex.coneLift B₀ ≫ toCone (a ≫ underMap F c) := by
        rw [Category.assoc, toCone_naturality_right]
    _ = Subcomplex.coneLift B₀ ≫ coneMap B₀.ι ≫ toCone b := by
        rw [w, toCone_naturality]
    _ = (Subcomplex.cone B₀).ι ≫ toCone b := by
        rw [← Category.assoc, Subcomplex.coneLift_coneMap_ι]

/-- A solution of the transposed lifting problem on cones gives a solution of the lifting
problem for `B₀ ↪ B` against `underMap F c`. -/
lemma exists_lift_underMap_of_cone {X Y B : SSet.{u}} (F : X ⟶ Y) (c : X _⦋0⦌)
    (B₀ : B.Subcomplex) (a : (B₀ : SSet.{u}) ⟶ (X.under c : SSet.{u}))
    (b : B ⟶ (Y.under (F.app _ c) : SSet.{u}))
    (h : ∃ l : cone B ⟶ X,
      (Subcomplex.cone B₀).ι ≫ l = Subcomplex.coneLift B₀ ≫ toCone a ∧ l ≫ F = toCone b) :
    ∃ l : B ⟶ (X.under c : SSet.{u}), B₀.ι ≫ l = a ∧ l ≫ underMap F c = b := by
  obtain ⟨l, hl₁, hl₂⟩ := h
  -- the solution upstairs sends the cone point to `c`, since the cone point lies in
  -- `Δ[0] ⋆ B₀`, where the solution restricts to `toCone a`
  have hpt : (conePt (B₀ : SSet.{u}) ≫ Subcomplex.coneToSub B₀) ≫
      (Subcomplex.cone B₀).ι = conePt B := by
    rw [Category.assoc, Subcomplex.coneToSub_ι, conePt_naturality]
  have hℓpt : conePt B ≫ l = const c := by
    rw [← hpt, Category.assoc, hl₁, Category.assoc,
      reassoc_of% (Subcomplex.coneToSub_coneLift B₀), conePt_comp_toCone]
  refine ⟨fromCone l hℓpt, ?_, ?_⟩
  · -- `B₀.ι ≫ lift = a`
    apply (coneHomEquiv _ X c).injective
    refine Subtype.ext ?_
    change toCone (B₀.ι ≫ fromCone l hℓpt) = toCone a
    rw [toCone_naturality, toCone_fromCone]
    calc coneMap B₀.ι ≫ l
        = Subcomplex.coneToSub B₀ ≫ (Subcomplex.cone B₀).ι ≫ l := by
          rw [← Category.assoc, Subcomplex.coneToSub_ι]
      _ = Subcomplex.coneToSub B₀ ≫ Subcomplex.coneLift B₀ ≫ toCone a := by
          rw [hl₁]
      _ = toCone a := by
          rw [← Category.assoc, Subcomplex.coneToSub_coneLift, Category.id_comp]
  · -- `lift ≫ underMap F c = b`
    apply (coneHomEquiv _ Y (F.app _ c)).injective
    refine Subtype.ext ?_
    change toCone (fromCone l hℓpt ≫ underMap F c) = toCone b
    rw [toCone_naturality_right, toCone_fromCone]
    exact hl₂

/-- The lifting problem for `∂Δ[n] ↪ Δ[n]` against `underMap F c`, solved by transposing it
across the universal property `coneHomEquiv` of the cone into a lifting problem for
`(Δ[0] ⋆ ∂Δ[n]) ↪ Δ[0] ⋆ Δ[n]` against `F`. -/
lemma hasLiftingProperty_boundary_underMap {X Y : SSet.{u}} (F : X ⟶ Y) [LeftFibration F]
    (c : X _⦋0⦌) (n : ℕ) : HasLiftingProperty (boundary.{u} n).ι (underMap F c) := by
  constructor
  intro a b sq
  -- the transposed lifting problem upstairs
  have sq' : CommSq (Subcomplex.coneLift ∂Δ[n] ≫ toCone a) (Subcomplex.cone ∂Δ[n]).ι F
      (toCone b) := ⟨coneLift_toCone_comp F c _ a b sq.w⟩
  have := hasLiftingProperty_cone_boundary_ι F n
  obtain ⟨l, hl₁, hl₂⟩ := exists_lift_underMap_of_cone F c _ a b
    ⟨sq'.lift, sq'.fac_left, sq'.fac_right⟩
  exact ⟨⟨⟨l, hl₁, hl₂⟩⟩⟩

/-! ### The main theorem -/

/-- **[Lur09, Proposition 2.1.2.5], non-relative form.** For a left fibration `F : X ⟶ Y` and a
vertex `c` of `X`, the induced map `underMap F c : X_{c/} ⟶ Y_{F c/}` is a trivial fibration:
it has the right lifting property against all monomorphisms. -/
theorem rlp_monomorphisms_underMap_of_leftFibration {X Y : SSet.{u}} (F : X ⟶ Y)
    [LeftFibration F] (c : X _⦋0⦌) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (underMap F c) := by
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  exact hasLiftingProperty_boundary_underMap F c n

end SSet
