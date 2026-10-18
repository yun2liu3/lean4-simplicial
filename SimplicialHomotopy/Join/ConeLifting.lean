/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.Cone

/-!
# Transferring lifting problems across the cone

[Lur09, Lemma 2.1.2.3] says that if `B₀ ↪ B` is left anodyne then
`(Δ[0] ⋆ B₀) ∪ (∅ ⋆ B) ↪ Δ[0] ⋆ B` is inner anodyne. Both classes are *by definition* left
lifting classes (`innerAnodyneExtensions = innerFibrations.llp`,
`leftAnodyneExtensions = leftFibrations.llp`), so the lemma needs no cell induction: it is the
statement that a lifting problem for `(Δ[0] ⋆ B₀) ∪ (∅ ⋆ B) ↪ Δ[0] ⋆ B` against `p : E ⟶ B'` is
*the same data* as a lifting problem for `B₀ ↪ B` against the relative undercategory projection

`relUnderProj p e : E_{e/} ⟶ B'_{p(e)/} ×_{B'} E`,

one for each vertex `e` of `E`. This is the two-variable adjunction argument that Mathlib uses
for the pushout-product (`SSet.anodyneExtensions_pushoutObjObjι`), with the cone
`Δ[0] ⋆ (−) ⊣ (−)_{c/}` of `Cone.lean` (`SSet.coneHomEquiv`) in place of `(− ⊗ −) ⊣ internalHom`.

* `SSet.relUnderProj` : the relative undercategory projection.
* `SSet.hasLiftingProperty_relUnderProj` : the forward transfer (a lifting problem for `B₀ ↪ B`
  against `relUnderProj p e` is solved by one for the cone union against `p`).
* `SSet.hasLiftingProperty_cone_sup` : the backward transfer.
* `SSet.innerAnodyneConeOfLeftAnodyne` : **[Lur09, 2.1.2.3]**, the two transfers applied on
  either side of the generating case `SSet.innerAnodyne_cone_horn` of `Cone.lean` (C4).
-/

universe u

open CategoryTheory Limits Opposite Simplicial

namespace SSet

variable {E B : SSet.{u}}

/-- The relative undercategory projection `E_{e/} ⟶ B_{p(e)/} ×_B E` of [Lur09, 2.1.2.2],
whose components are `underMap p e` and `E.underProj e`. -/
noncomputable def relUnderProj (p : E ⟶ B) (e : E _⦋0⦌) :
    (E.under e : SSet.{u}) ⟶ pullback (B.underProj (p.app _ e)) p :=
  pullback.lift (underMap p e) (E.underProj e) (underMap_underProj p e)

@[reassoc (attr := simp)]
lemma relUnderProj_fst (p : E ⟶ B) (e : E _⦋0⦌) :
    relUnderProj p e ≫ pullback.fst _ _ = underMap p e :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relUnderProj_snd (p : E ⟶ B) (e : E _⦋0⦌) :
    relUnderProj p e ≫ pullback.snd _ _ = E.underProj e :=
  pullback.lift_snd _ _ _

/-! ### The forward transfer -/

/-- **Forward transfer of a lifting problem across the cone.** If the inclusion
`(Δ[0] ⋆ Y₀) ∪ (∅ ⋆ Y) ↪ Δ[0] ⋆ Y` has the left lifting property against
`p : E ⟶ B`, then `Y₀ ↪ Y` has the left lifting property against the relative
undercategory projection `relUnderProj p e` of [Lur09, 2.1.2.2], for every
vertex `e` of `E`.

This is the `B = Δ[0]` case `hasLiftingProperty_horn_ι_underProj` of `Cone.lean`
with `terminal.from C` replaced by a general `p`: the lifting problem is
transported across the universal property `coneHomEquiv` of the cone. -/
lemma hasLiftingProperty_relUnderProj {Y : SSet.{u}} (Y₀ : Y.Subcomplex)
    (p : E ⟶ B) (e : E _⦋0⦌)
    (h : HasLiftingProperty (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι p) :
    HasLiftingProperty Y₀.ι (relUnderProj p e) := by
  constructor
  intro a b sq
  -- the two components of the lifting problem downstairs, named opaquely
  obtain ⟨β, hβ⟩ : ∃ β, β = b ≫ pullback.snd (B.underProj (p.app _ e)) p := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = b ≫ pullback.fst (B.underProj (p.app _ e)) p := ⟨_, rfl⟩
  have hfst : a ≫ underMap p e = Y₀.ι ≫ b' := by
    rw [hb']
    simpa using sq.w =≫ pullback.fst (B.underProj (p.app _ e)) p
  have hsnd : a ≫ E.underProj e = Y₀.ι ≫ β := by
    rw [hβ]
    simpa using sq.w =≫ pullback.snd (B.underProj (p.app _ e)) p
  have hcond : β ≫ p = b' ≫ B.underProj (p.app _ e) := by
    rw [hβ, hb', Category.assoc, Category.assoc, pullback.condition]
  -- the map `(Δ[0] ⋆ Y₀) ∪ (∅ ⋆ Y) ⟶ E` glued from `toCone a` and `β`
  have bsq : Subcomplex.BicartSq
      (Subcomplex.cone Y₀ ⊓ Subcomplex.range (coneι Y))
      (Subcomplex.cone Y₀) (Subcomplex.range (coneι Y))
      (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)) := ⟨rfl, rfl⟩
  have hφ₂ : Subcomplex.toRange (coneι Y) ≫
      (inv (Subcomplex.toRange (coneι Y)) ≫ β) = β := by
    simp only [IsIso.hom_inv_id_assoc]
  have w : Subcomplex.homOfLE bsq.le₁₂ ≫ (Subcomplex.coneLift Y₀ ≫ toCone a) =
      Subcomplex.homOfLE bsq.le₁₃ ≫ (inv (Subcomplex.toRange (coneι Y)) ≫ β) := by
    refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
    obtain ⟨x, hx₁, y, rfl⟩ := x
    have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app hφ₂ m) y
    change (inv (Subcomplex.toRange (coneι Y)) ≫ β).app m ⟨(coneι _).app m y, y, rfl⟩ =
      β.app m y at h₂
    change toConeFun a (ConeSimplex.ofSimplex ⟨y, hx₁⟩) =
      (inv (Subcomplex.toRange (coneι Y)) ≫ β).app m ⟨(coneι _).app m y, y, rfl⟩
    rw [h₂]
    have h₁ :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (coneι_comp_toCone a) m) ⟨y, hx₁⟩
    change toConeFun a (ConeSimplex.ofSimplex ⟨y, hx₁⟩) =
      (E.underProj e).app m (a.app m ⟨y, hx₁⟩) at h₁
    rw [h₁]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hsnd m) ⟨y, hx₁⟩
  have hφ₁ := bsq.isPushout.inl_desc _ _ w
  have hφ₂' := bsq.isPushout.inr_desc _ _ w
  -- the glued map is a lifting problem for `p` upstairs, with lower edge `toCone b'`
  have wsq : bsq.isPushout.desc _ _ w ≫ p =
      (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι ≫ toCone b' := by
    refine bsq.isPushout.hom_ext ?_ ?_
    · rw [← Category.assoc, bsq.isPushout.inl_desc]
      calc (Subcomplex.coneLift Y₀ ≫ toCone a) ≫ p
          = Subcomplex.coneLift Y₀ ≫ toCone (a ≫ underMap p e) := by
            rw [Category.assoc, toCone_naturality_right]
        _ = Subcomplex.coneLift Y₀ ≫ coneMap Y₀.ι ≫ toCone b' := by
            rw [hfst, toCone_naturality]
        _ = (Subcomplex.cone Y₀).ι ≫ toCone b' := by
            rw [← Category.assoc, Subcomplex.coneLift_coneMap_ι]
        _ = Subcomplex.homOfLE bsq.le₂₄ ≫
              (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι ≫ toCone b' := rfl
    · rw [← Category.assoc, bsq.isPushout.inr_desc]
      calc (inv (Subcomplex.toRange (coneι Y)) ≫ β) ≫ p
          = inv (Subcomplex.toRange (coneι Y)) ≫ coneι Y ≫ toCone b' := by
            rw [Category.assoc, coneι_comp_toCone, hcond]
        _ = inv (Subcomplex.toRange (coneι Y)) ≫ Subcomplex.toRange (coneι Y) ≫
              (Subcomplex.range (coneι Y)).ι ≫ toCone b' := rfl
        _ = (Subcomplex.range (coneι Y)).ι ≫ toCone b' := by rw [IsIso.inv_hom_id_assoc]
        _ = Subcomplex.homOfLE bsq.le₃₄ ≫
              (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι ≫ toCone b' := rfl
  have sq' : CommSq (bsq.isPushout.desc _ _ w)
      (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι p (toCone b') := ⟨wsq⟩
  have := h.sq_hasLift sq'
  have hℓ := sq'.fac_left
  -- the lift sends the cone point to `e`
  have hℓpt : conePt _ ≫ sq'.lift = const e := by
    refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hℓ m)
      ⟨ConeSimplex.pt _ m.unop.len, Or.inl (Subcomplex.pt_mem_cone Y₀ m)⟩
    change sq'.lift.app m (ConeSimplex.pt _ m.unop.len) =
      (bsq.isPushout.desc _ _ w).app m ⟨_, _⟩ at h
    have h' := ConcreteCategory.congr_hom (NatTrans.congr_app hφ₁ m)
      ⟨ConeSimplex.pt _ m.unop.len, Subcomplex.pt_mem_cone Y₀ m⟩
    change (bsq.isPushout.desc _ _ w).app m ⟨_, _⟩ =
      toConeFun a (ConeSimplex.pt _ m.unop.len) at h'
    change sq'.lift.app m (ConeSimplex.pt _ m.unop.len) = (const e : Δ[0] ⟶ E).app m t
    rw [h, h']
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (conePt_comp_toCone a) m) t
  refine ⟨⟨⟨fromCone sq'.lift hℓpt, ?_, ?_⟩⟩⟩
  · -- `Y₀.ι ≫ lift = a`
    apply (coneHomEquiv _ E e).injective
    refine Subtype.ext ?_
    change toCone (Y₀.ι ≫ fromCone sq'.lift hℓpt) = toCone a
    rw [toCone_naturality, toCone_fromCone]
    calc coneMap Y₀.ι ≫ sq'.lift
        = Subcomplex.coneToSub Y₀ ≫ (Subcomplex.cone Y₀).ι ≫ sq'.lift := by
          rw [← Category.assoc, Subcomplex.coneToSub_ι]
      _ = Subcomplex.coneToSub Y₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫
            (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι ≫ sq'.lift := rfl
      _ = Subcomplex.coneToSub Y₀ ≫ (Subcomplex.coneLift Y₀ ≫ toCone a) := by
          rw [hℓ, hφ₁]
      _ = toCone a := by
          rw [← Category.assoc, Subcomplex.coneToSub_coneLift, Category.id_comp]
  · -- `lift ≫ relUnderProj p e = b`
    refine pullback.hom_ext ?_ ?_
    · -- the `B_{p(e)/}` component
      rw [Category.assoc, relUnderProj_fst, ← hb']
      apply (coneHomEquiv _ B (p.app _ e)).injective
      refine Subtype.ext ?_
      change toCone (fromCone sq'.lift hℓpt ≫ underMap p e) = toCone b'
      rw [toCone_naturality_right, toCone_fromCone]
      exact sq'.fac_right
    · -- the `E` component
      rw [Category.assoc, relUnderProj_snd, ← hβ, ← coneι_comp_toCone, toCone_fromCone]
      calc coneι Y ≫ sq'.lift
          = Subcomplex.toRange (coneι Y) ≫ (Subcomplex.range (coneι Y)).ι ≫ sq'.lift := rfl
        _ = Subcomplex.toRange (coneι Y) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫
              (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι ≫ sq'.lift := rfl
        _ = Subcomplex.toRange (coneι Y) ≫ (inv (Subcomplex.toRange (coneι Y)) ≫ β) := by
            rw [hℓ, hφ₂']
        _ = β := hφ₂

/-! ### The backward transfer -/

/-- Every morphism `Δ[0] ⟶ X` is the constant morphism at a vertex of `X`; this is Yoneda
(`SSet.yonedaEquiv_symm_zero`) in degree `0`. -/
lemma exists_eq_const_of_stdSimplex_zero {X : SSet.{u}} (f : Δ[0] ⟶ X) :
    ∃ x : X _⦋0⦌, f = const x :=
  ⟨yonedaEquiv f, by rw [← yonedaEquiv_symm_zero, Equiv.symm_apply_apply]⟩

/-- `Subcomplex.coneToSub A : Δ[0] ⋆ A ⟶ Subcomplex.cone A` is an isomorphism
(`Subcomplex.coneLift_coneToSub`), so it can be cancelled on the left. -/
lemma coneBwd_cancel_coneToSub {K : SSet.{u}} (A : K.Subcomplex) {X : SSet.{u}}
    {f g : (Subcomplex.cone A : SSet.{u}) ⟶ X}
    (h : Subcomplex.coneToSub A ≫ f = Subcomplex.coneToSub A ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, ← Subcomplex.coneLift_coneToSub A,
    Category.assoc, Category.assoc, h]

/-- The backward transfer of a lifting problem across the cone: if `Y₀ ↪ Y` has the lifting
property against the relative undercategory projection `relUnderProj p e` for *every* vertex `e`
of `E`, then the cone union `(Δ[0] ⋆ Y₀) ∪ (∅ ⋆ Y) ↪ Δ[0] ⋆ Y` has the
lifting property against `p`. -/
lemma hasLiftingProperty_cone_sup {Y : SSet.{u}} (Y₀ : Y.Subcomplex) (p : E ⟶ B)
    (h : ∀ e : E _⦋0⦌, HasLiftingProperty Y₀.ι (relUnderProj p e)) :
    HasLiftingProperty (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι p := by
  constructor
  intro a b sq
  have bsq : Subcomplex.BicartSq (Subcomplex.cone Y₀ ⊓ Subcomplex.range (coneι Y))
      (Subcomplex.cone Y₀) (Subcomplex.range (coneι Y))
      (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)) := ⟨rfl, rfl⟩
  -- the two summands of the commutative square `sq`
  have haι : Subcomplex.homOfLE bsq.le₂₄ ≫ a ≫ p = (Subcomplex.cone Y₀).ι ≫ b := by
    rw [sq.w, ← Category.assoc, Subcomplex.homOfLE_ι]
  have hbι : Subcomplex.homOfLE bsq.le₃₄ ≫ a ≫ p =
      (Subcomplex.range (coneι Y)).ι ≫ b := by
    rw [sq.w, ← Category.assoc, Subcomplex.homOfLE_ι]
  -- Step 1: the vertex `e` of `E` that the cone point is sent to
  obtain ⟨e, he⟩ : ∃ e : E _⦋0⦌, conePt (Y₀ : SSet.{u}) ≫
      (Subcomplex.coneToSub Y₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫ a) = const e :=
    exists_eq_const_of_stdSimplex_zero _
  -- Step 2: the induced lifting problem for `relUnderProj p e`
  obtain ⟨α, hα⟩ : ∃ α : (Y₀ : SSet.{u}) ⟶ (E.under e : SSet.{u}),
      toCone α = Subcomplex.coneToSub Y₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫ a :=
    ⟨fromCone _ he, toCone_fromCone _ he⟩
  have hbpt : conePt Y ≫ b = const (p.app (op ⦋0⦌) e) := by
    rw [← const_comp, ← he, ← conePt_naturality Y₀.ι, ← Subcomplex.coneToSub_ι Y₀]
    simp only [Category.assoc]
    rw [← haι]
  obtain ⟨b', hb'⟩ : ∃ b' : Y ⟶ (B.under (p.app (op ⦋0⦌) e) : SSet.{u}),
      toCone b' = b :=
    ⟨fromCone b hbpt, toCone_fromCone b hbpt⟩
  have hβ : coneι Y ≫ b =
      (Subcomplex.toRange (coneι Y) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a) ≫ p := by
    simp only [Category.assoc]
    rw [hbι, ← Category.assoc, Subcomplex.toRange_ι]
  have hlift : b' ≫ B.underProj (p.app (op ⦋0⦌) e) =
      (Subcomplex.toRange (coneι Y) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a) ≫ p := by
    rw [← coneι_comp_toCone b', hb']
    exact hβ
  obtain ⟨bY, hbY₁, hbY₂⟩ : ∃ bY : Y ⟶ pullback (B.underProj (p.app (op ⦋0⦌) e)) p,
      bY ≫ pullback.fst _ _ = b' ∧ bY ≫ pullback.snd _ _ =
        Subcomplex.toRange (coneι Y) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a :=
    ⟨pullback.lift _ _ hlift, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have sq₂ : CommSq α Y₀.ι (relUnderProj p e) bY := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relUnderProj_fst, hbY₁]
      -- `α ≫ underMap p e = Y₀.ι ≫ b'`, both sides seen through `toCone`
      apply (coneHomEquiv _ B (p.app (op ⦋0⦌) e)).injective
      refine Subtype.ext ?_
      change toCone (α ≫ underMap p e) = toCone (Y₀.ι ≫ b')
      rw [toCone_naturality_right, toCone_naturality, hα, hb', ← Subcomplex.coneToSub_ι Y₀]
      simp only [Category.assoc]
      rw [haι]
    · simp only [Category.assoc, relUnderProj_snd, hbY₂]
      -- `α ≫ E.underProj e = Y₀.ι ≫ β`, both sides restrictions of `a`
      rw [← coneι_comp_toCone α, hα]
      have key : coneι (Y₀ : SSet.{u}) ≫ Subcomplex.coneToSub Y₀ ≫
          Subcomplex.homOfLE bsq.le₂₄ =
          Y₀.ι ≫ Subcomplex.toRange (coneι Y) ≫ Subcomplex.homOfLE bsq.le₃₄ := by
        rw [← cancel_mono (Subcomplex.cone Y₀ ⊔ Subcomplex.range (coneι Y)).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.coneToSub_ι,
          Subcomplex.toRange_ι, coneι_naturality]
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ a) key
  have hie : HasLiftingProperty Y₀.ι (relUnderProj p e) := h e
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : Y ⟶ (E.under e : SSet.{u}),
      Y₀.ι ≫ γ = α ∧ γ ≫ relUnderProj p e = bY :=
    ⟨sq₂.lift, sq₂.fac_left, sq₂.fac_right⟩
  -- Step 3: the lift is `toCone γ`
  refine ⟨⟨⟨toCone γ, ?_, ?_⟩⟩⟩
  · refine bsq.isPushout.hom_ext ?_ ?_
    · rw [← Category.assoc, Subcomplex.homOfLE_ι]
      refine coneBwd_cancel_coneToSub Y₀ ?_
      conv_lhs => rw [← Category.assoc, Subcomplex.coneToSub_ι]
      rw [← toCone_naturality, hγ₁, hα]
    · rw [← Category.assoc, Subcomplex.homOfLE_ι,
        ← cancel_epi (Subcomplex.toRange (coneι Y))]
      conv_lhs => rw [← Category.assoc, Subcomplex.toRange_ι]
      rw [coneι_comp_toCone, ← relUnderProj_snd p e, ← Category.assoc, hγ₂, hbY₂]
  · rw [← toCone_naturality_right, ← relUnderProj_fst p e, ← Category.assoc]
    rw [hγ₂, hbY₁, hb']

/-! ### [Lur09, Lemma 2.1.2.3] -/

/-- **[Lur09, Lemma 2.1.2.3]**: if `B₀ ↪ B` is left anodyne, then
`(Δ[0] ⋆ B₀) ∪ (∅ ⋆ B) ↪ Δ[0] ⋆ B` is inner anodyne.

The proof uses no cell induction. Both classes are left lifting classes *by definition*
(`innerAnodyneExtensions = innerFibrations.llp`, `leftAnodyneExtensions = leftFibrations.llp`), so
after unfolding we must lift against an arbitrary inner fibration `p`; `hasLiftingProperty_cone_sup`
turns that into a lifting problem for `B₀ ↪ B` against `relUnderProj p e`, which the left anodyne
hypothesis solves as soon as `relUnderProj p e` is a left fibration — and *that* is checked on the
generating left horns by running `hasLiftingProperty_relUnderProj` in the other direction and
appealing to `innerAnodyne_cone_horn` (C4).

In particular [Lur09, 2.1.2.2] (`leftFibration_underProj_of_innerAnodyne_cone`) is not used
here: the single instance of it that the argument needs is proved from the horn case. -/
theorem innerAnodyneConeOfLeftAnodyne : InnerAnodyneConeOfLeftAnodyne.{u} := by
  intro Y Y₀ hY₀ E B p hp
  refine hasLiftingProperty_cone_sup Y₀ p fun e ↦ ?_
  refine hY₀ _ ?_
  rintro _ _ _ ⟨i, hi⟩
  exact hasLiftingProperty_relUnderProj _ p e (innerAnodyne_cone_horn i hi p hp)

end SSet
