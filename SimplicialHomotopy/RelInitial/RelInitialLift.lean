/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.RelInitial.RelInitial
import SimplicialHomotopy.Fibration.Cocartesian
import SimplicialHomotopy.Slice.UnderMapLeftFibration
import SimplicialHomotopy.Join.ConeLifting

/-!
# Cocartesian cone edges are relatively initial

Let `F : C ⟶ S` be a morphism of simplicial sets, `c` a vertex of `C`, and
`U = underMap F c : C_{c/} ⟶ S_{F c/}`. A vertex `y` of `C_{c/}` is a `1`-simplex `y.1 : c → y₁`
of `C`, its *cone edge*. This file proves:

* (A) `SSet.IsRelInitial.hasConeLiftAt` : a `p`-initial vertex solves every cone-shaped lifting
  problem `(Δ[0] ⋆ B₀) ∪ B ↪ Δ[0] ⋆ B`, for every subcomplex `B₀ ⊆ B`, not only boundaries.
  Via the universal property of the cone (`SSet.coneHomEquiv`), such problems at `y` are the
  same data as lifting problems for `B₀ ↪ B` against `relUnderProj p y`
  (`SSet.hasLiftingProperty_relUnderProj_of_hasConeLiftAt` and
  `SSet.hasConeLiftAt_of_hasLiftingProperty_relUnderProj`, the fixed-vertex versions of the
  two transfers of `Join/ConeLifting.lean`), and `SSet.rlp_monomorphisms` passes from
  boundaries to all monomorphisms.
* (B) `SSet.coneUnion_boundary_eq_preimage` : `(Δ[0] ⋆ ∂Δ[n]) ∪ Δ[n]` is `∂Δ[n + 1]` under
  `stdSimplex.coneIso n`.
* (C) `SSet.isRelInitial_underMap` : if the cone edge of `y` is `F`-cocartesian then `y` is
  `U`-initial. The key step `SSet.exists_lift_boundary_underMap` solves a lifting problem for
  `∂Δ[n + 1] ↪ Δ[n + 1]` against `U` whose vertex `0` goes to a vertex with cocartesian cone edge:
  transposed across the cone it is the left horn problem `Λ[n + 2, 0] ↪ Δ[n + 2]` against `F`
  with initial edge that cone edge (`SSet.coneIso_inv_edge₀₁`), which `IsCocartesianEdge` solves.
  `SSet.hasConeLiftAt_boundary_of_exists_lift` identifies `HasConeLiftAt p y ∂Δ[n]` with such
  boundary problems, via (B). Both transports along `stdSimplex.coneIso` go through
  `SSet.Subcomplex.exists_lift_of_preimageIso`, and the transposition across the cone through
  `SSet.exists_lift_underMap_of_cone` (`Slice/UnderMapLeftFibration.lean`).
* (D) `SSet.underCocart F c` : the full subcomplex `C_{c/}^♮` of `C_{c/}` on the vertices with
  `F`-cocartesian cone edge (`SSet.mem_underCocart_vertex_iff`).
* (E) `SSet.rlp_monomorphisms_underCocart` : for a cocartesian fibration `F`, the restriction
  `C_{c/}^♮ ⟶ S_{F c/}` of `U` is a trivial fibration.

Nothing here uses `Cofinal/HTT.lean`.
-/

universe u

open CategoryTheory Limits Opposite Simplicial

namespace SSet

variable {X Y B : SSet.{u}}

/-- The cone point of `coneUnion B₀` factors through `Δ[0] ⋆ B₀`. -/
lemma conePtUnion_eq (B₀ : B.Subcomplex) :
    conePtUnion B₀ = conePt (B₀ : SSet.{u}) ≫ Subcomplex.coneToSub B₀ ≫
      Subcomplex.homOfLE (le_sup_left : Subcomplex.cone B₀ ≤ coneUnion B₀) := by
  rw [← cancel_mono (coneUnion B₀).ι]
  simp only [conePtUnion_ι, Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.coneToSub_ι,
    conePt_naturality]

/-- **Forward transfer at a fixed vertex.** `HasConeLiftAt p y B₀` gives the lifting property of
`B₀ ↪ B` against the relative undercategory projection `relUnderProj p y`. -/
lemma hasLiftingProperty_relUnderProj_of_hasConeLiftAt {p : X ⟶ Y} {y : X _⦋0⦌}
    {B₀ : B.Subcomplex} (h : HasConeLiftAt p y B₀) :
    HasLiftingProperty B₀.ι (relUnderProj p y) := by
  constructor
  intro a b sq
  obtain ⟨β, hβ⟩ : ∃ β, β = b ≫ pullback.snd (Y.underProj (p.app _ y)) p := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = b ≫ pullback.fst (Y.underProj (p.app _ y)) p := ⟨_, rfl⟩
  have hfst : a ≫ underMap p y = B₀.ι ≫ b' := by
    rw [hb']
    simpa using sq.w =≫ pullback.fst (Y.underProj (p.app _ y)) p
  have hsnd : a ≫ X.underProj y = B₀.ι ≫ β := by
    rw [hβ]
    simpa using sq.w =≫ pullback.snd (Y.underProj (p.app _ y)) p
  have hcond : β ≫ p = b' ≫ Y.underProj (p.app _ y) := by
    rw [hβ, hb', Category.assoc, Category.assoc, pullback.condition]
  have bsq : Subcomplex.BicartSq
      (Subcomplex.cone B₀ ⊓ Subcomplex.range (coneι B))
      (Subcomplex.cone B₀) (Subcomplex.range (coneι B))
      (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)) := ⟨rfl, rfl⟩
  have hφ₂ : Subcomplex.toRange (coneι B) ≫
      (inv (Subcomplex.toRange (coneι B)) ≫ β) = β := by
    simp only [IsIso.hom_inv_id_assoc]
  have w : Subcomplex.homOfLE bsq.le₁₂ ≫ (Subcomplex.coneLift B₀ ≫ toCone a) =
      Subcomplex.homOfLE bsq.le₁₃ ≫ (inv (Subcomplex.toRange (coneι B)) ≫ β) := by
    refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
    obtain ⟨x, hx₁, z, rfl⟩ := x
    have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app hφ₂ m) z
    change (inv (Subcomplex.toRange (coneι B)) ≫ β).app m ⟨(coneι _).app m z, z, rfl⟩ =
      β.app m z at h₂
    change toConeFun a (ConeSimplex.ofSimplex ⟨z, hx₁⟩) =
      (inv (Subcomplex.toRange (coneι B)) ≫ β).app m ⟨(coneι _).app m z, z, rfl⟩
    rw [h₂]
    have h₁ :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (coneι_comp_toCone a) m) ⟨z, hx₁⟩
    change toConeFun a (ConeSimplex.ofSimplex ⟨z, hx₁⟩) =
      (X.underProj y).app m (a.app m ⟨z, hx₁⟩) at h₁
    rw [h₁]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hsnd m) ⟨z, hx₁⟩
  have hφ₁ := bsq.isPushout.inl_desc _ _ w
  have wsq : bsq.isPushout.desc _ _ w ≫ p =
      (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι ≫ toCone b' := by
    refine bsq.isPushout.hom_ext ?_ ?_
    · rw [← Category.assoc, bsq.isPushout.inl_desc]
      exact coneLift_toCone_comp p y B₀ a b' hfst
    · rw [← Category.assoc, bsq.isPushout.inr_desc]
      calc (inv (Subcomplex.toRange (coneι B)) ≫ β) ≫ p
          = inv (Subcomplex.toRange (coneι B)) ≫ coneι B ≫ toCone b' := by
            rw [Category.assoc, coneι_comp_toCone, hcond]
        _ = inv (Subcomplex.toRange (coneι B)) ≫ Subcomplex.toRange (coneι B) ≫
              (Subcomplex.range (coneι B)).ι ≫ toCone b' := rfl
        _ = (Subcomplex.range (coneι B)).ι ≫ toCone b' := by rw [IsIso.inv_hom_id_assoc]
        _ = Subcomplex.homOfLE bsq.le₃₄ ≫
              (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι ≫ toCone b' := rfl
  -- the cone point goes to `y`
  have hpt : conePtUnion B₀ ≫ bsq.isPushout.desc _ _ w = const y := by
    rw [conePtUnion_eq, Category.assoc, Category.assoc]
    rw [bsq.isPushout.inl_desc]
    rw [reassoc_of% (Subcomplex.coneToSub_coneLift B₀), conePt_comp_toCone]
  obtain ⟨l, hℓ, hℓp⟩ := h _ _ wsq hpt
  have hℓpt : conePt B ≫ l = const y := by
    rw [← conePtUnion_ι B₀, Category.assoc, hℓ, hpt]
  refine ⟨⟨⟨fromCone l hℓpt, ?_, ?_⟩⟩⟩
  · apply (coneHomEquiv _ X y).injective
    refine Subtype.ext ?_
    change toCone (B₀.ι ≫ fromCone l hℓpt) = toCone a
    rw [toCone_naturality, toCone_fromCone]
    calc coneMap B₀.ι ≫ l
        = Subcomplex.coneToSub B₀ ≫ (Subcomplex.cone B₀).ι ≫ l := by
          rw [← Category.assoc, Subcomplex.coneToSub_ι]
      _ = Subcomplex.coneToSub B₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫
            (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι ≫ l := rfl
      _ = Subcomplex.coneToSub B₀ ≫ (Subcomplex.coneLift B₀ ≫ toCone a) := by
          rw [hℓ, hφ₁]
      _ = toCone a := by
          rw [← Category.assoc, Subcomplex.coneToSub_coneLift, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, relUnderProj_fst, ← hb']
      apply (coneHomEquiv _ Y (p.app _ y)).injective
      refine Subtype.ext ?_
      change toCone (fromCone l hℓpt ≫ underMap p y) = toCone b'
      rw [toCone_naturality_right, toCone_fromCone]
      exact hℓp
    · rw [Category.assoc, relUnderProj_snd, ← hβ, ← coneι_comp_toCone, toCone_fromCone]
      calc coneι B ≫ l
          = Subcomplex.toRange (coneι B) ≫ (Subcomplex.range (coneι B)).ι ≫ l := rfl
        _ = Subcomplex.toRange (coneι B) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫
              (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι ≫ l := rfl
        _ = Subcomplex.toRange (coneι B) ≫
              (inv (Subcomplex.toRange (coneι B)) ≫ β) := by
            rw [hℓ, bsq.isPushout.inr_desc]
        _ = β := hφ₂

/-- **Backward transfer at a fixed vertex.** The lifting property of `B₀ ↪ B` against
`relUnderProj p y` gives `HasConeLiftAt p y B₀`. -/
lemma hasConeLiftAt_of_hasLiftingProperty_relUnderProj {p : X ⟶ Y} {y : X _⦋0⦌} {B₀ : B.Subcomplex}
    (h : HasLiftingProperty B₀.ι (relUnderProj p y)) : HasConeLiftAt p y B₀ := by
  intro a b sqw hpt
  have bsq : Subcomplex.BicartSq (Subcomplex.cone B₀ ⊓ Subcomplex.range (coneι B))
      (Subcomplex.cone B₀) (Subcomplex.range (coneι B))
      (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)) := ⟨rfl, rfl⟩
  have haι : Subcomplex.homOfLE bsq.le₂₄ ≫ a ≫ p = (Subcomplex.cone B₀).ι ≫ b := by
    rw [sqw, ← Category.assoc, Subcomplex.homOfLE_ι]
  have hbι : Subcomplex.homOfLE bsq.le₃₄ ≫ a ≫ p =
      (Subcomplex.range (coneι B)).ι ≫ b := by
    rw [sqw, ← Category.assoc, Subcomplex.homOfLE_ι]
  have he : conePt (B₀ : SSet.{u}) ≫
      (Subcomplex.coneToSub B₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫ a) = const y := by
    rw [← hpt, conePtUnion_eq]
    simp only [Category.assoc]
  obtain ⟨α, hα⟩ : ∃ α : (B₀ : SSet.{u}) ⟶ (X.under y : SSet.{u}),
      toCone α = Subcomplex.coneToSub B₀ ≫ Subcomplex.homOfLE bsq.le₂₄ ≫ a :=
    ⟨fromCone _ he, toCone_fromCone _ he⟩
  have hbpt : conePt B ≫ b = const (p.app (op ⦋0⦌) y) := by
    rw [← const_comp, ← he, ← conePt_naturality B₀.ι, ← Subcomplex.coneToSub_ι B₀]
    simp only [Category.assoc]
    rw [← haι]
  obtain ⟨b', hb'⟩ : ∃ b' : B ⟶ (Y.under (p.app (op ⦋0⦌) y) : SSet.{u}),
      toCone b' = b :=
    ⟨fromCone b hbpt, toCone_fromCone b hbpt⟩
  have hβ : coneι B ≫ b =
      (Subcomplex.toRange (coneι B) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a) ≫ p := by
    simp only [Category.assoc]
    rw [hbι, ← Category.assoc, Subcomplex.toRange_ι]
  have hlift : b' ≫ Y.underProj (p.app (op ⦋0⦌) y) =
      (Subcomplex.toRange (coneι B) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a) ≫ p := by
    rw [← coneι_comp_toCone b', hb']
    exact hβ
  obtain ⟨bY, hbY₁, hbY₂⟩ : ∃ bY : B ⟶ pullback (Y.underProj (p.app (op ⦋0⦌) y)) p,
      bY ≫ pullback.fst _ _ = b' ∧ bY ≫ pullback.snd _ _ =
        Subcomplex.toRange (coneι B) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫ a :=
    ⟨pullback.lift _ _ hlift, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have sq₂ : CommSq α B₀.ι (relUnderProj p y) bY := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relUnderProj_fst, hbY₁]
      apply (coneHomEquiv _ Y (p.app (op ⦋0⦌) y)).injective
      refine Subtype.ext ?_
      change toCone (α ≫ underMap p y) = toCone (B₀.ι ≫ b')
      rw [toCone_naturality_right, toCone_naturality, hα, hb', ← Subcomplex.coneToSub_ι B₀]
      simp only [Category.assoc]
      rw [haι]
    · simp only [Category.assoc, relUnderProj_snd, hbY₂]
      rw [← coneι_comp_toCone α, hα]
      have key : coneι (B₀ : SSet.{u}) ≫ Subcomplex.coneToSub B₀ ≫
          Subcomplex.homOfLE bsq.le₂₄ =
          B₀.ι ≫ Subcomplex.toRange (coneι B) ≫ Subcomplex.homOfLE bsq.le₃₄ := by
        rw [← cancel_mono (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.coneToSub_ι,
          Subcomplex.toRange_ι, coneι_naturality]
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ a) key
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : B ⟶ (X.under y : SSet.{u}),
      B₀.ι ≫ γ = α ∧ γ ≫ relUnderProj p y = bY :=
    ⟨sq₂.lift, sq₂.fac_left, sq₂.fac_right⟩
  refine ⟨toCone γ, ?_, ?_⟩
  · refine bsq.isPushout.hom_ext ?_ ?_
    · rw [← Category.assoc, Subcomplex.homOfLE_ι]
      refine coneBwd_cancel_coneToSub B₀ ?_
      conv_lhs => rw [← Category.assoc, Subcomplex.coneToSub_ι]
      rw [← toCone_naturality, hγ₁, hα]
    · rw [← Category.assoc, Subcomplex.homOfLE_ι,
        ← cancel_epi (Subcomplex.toRange (coneι B))]
      conv_lhs => rw [← Category.assoc, Subcomplex.toRange_ι]
      rw [coneι_comp_toCone, ← relUnderProj_snd p y, ← Category.assoc, hγ₂, hbY₂]
  · rw [← toCone_naturality_right, ← relUnderProj_fst p y, ← Category.assoc]
    rw [hγ₂, hbY₁, hb']

/-- **(A)** A `p`-initial vertex `y` solves every cone-shaped lifting problem, for every
subcomplex `B₀ ⊆ B` (not only boundaries): the relative undercategory projection
`relUnderProj p y` lifts against every `∂Δ[n] ↪ Δ[n]`, hence against every monomorphism. -/
theorem IsRelInitial.hasConeLiftAt {p : X ⟶ Y} {y : X _⦋0⦌}
    (h : IsRelInitial p y) (B₀ : B.Subcomplex) : HasConeLiftAt p y B₀ := by
  have hrlp : (MorphismProperty.monomorphisms SSet.{u}).rlp (relUnderProj p y) := by
    rw [SSet.rlp_monomorphisms]
    rintro _ _ _ ⟨n⟩
    exact hasLiftingProperty_relUnderProj_of_hasConeLiftAt (h n)
  exact hasConeLiftAt_of_hasLiftingProperty_relUnderProj
    (hrlp _ (MorphismProperty.monomorphisms.infer_property B₀.ι))

open stdSimplex in
/-- **(B)** Under `stdSimplex.coneIso n : Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, the subcomplex
`(Δ[0] ⋆ ∂Δ[n]) ∪ Δ[n]` is the boundary `∂Δ[n + 1]`: a simplex of `Δ[n + 1]` misses a vertex iff
it misses `0` (it lies in the base `Δ[n]`) or its residual part misses a vertex of `Δ[n]`. -/
lemma coneUnion_boundary_eq_preimage (n : ℕ) :
    coneUnion (boundary.{u} n) = (boundary.{u} (n + 1)).preimage (stdSimplex.coneIso n).hom := by
  ext m x
  obtain ⟨⟨p⟩⟩ := m
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    show (ConcreteCategory.hom ((coneIso.{u} n).hom.app (op ⦋p⦌))) x
        = objMk ((coneAug n x.y).comp (collapse x.j x.k x.hjk)) from
      toConeFun_toUnderVertex₀ _ _,
    mem_boundary_iff_notMem_range, Subfunctor.max_obj, Set.mem_union,
    Subcomplex.mem_cone_iff, Subcomplex.mem_range_coneι_iff]
  obtain ⟨j, k, hjk, y⟩ := x
  dsimp only at hjk ⊢
  rw [show Set.range
      ⇑(objMk ((coneAug n y).comp (collapse j k hjk)) : Δ[n + 1] _⦋p⦌) =
      Set.range (fun t ↦ coneAug n y (collapse j k hjk t)) from rfl]
  cases k with
  | zero =>
    refine iff_of_true (Or.inl trivial) ⟨Fin.succ 0, ?_⟩
    rintro ⟨t, ht⟩
    exact Fin.succ_ne_zero 0 ht.symm
  | succ k' =>
    have hzero : coneAug n y 0 = 0 := (coneAug_eq_zero_iff _ y 0).2 rfl
    have hsucc : ∀ t : Fin (k' + 1), coneAug n y t.succ = (asOrderHom y t).succ :=
      fun _ ↦ rfl
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine iff_of_true (Or.inr rfl) ⟨0, ?_⟩
      rintro ⟨t, ht⟩
      have h : collapse 0 (k' + 1) hjk t ≠ 0 := by
        rw [Ne, Fin.ext_iff, collapse_apply_val]
        simp
      exact h ((coneAug_eq_zero_iff _ y _).1 ht)
    · rw [or_iff_left (show j ≠ 0 by omega)]
      refine Iff.trans (mem_boundary_iff_notMem_range (n := n) (d := k') y) ?_
      constructor
      · rintro ⟨v, hvr⟩
        refine ⟨v.succ, ?_⟩
        rintro ⟨t, ht⟩
        dsimp only at ht
        rcases Fin.eq_zero_or_eq_succ (collapse j (k' + 1) hjk t) with h | ⟨s, h⟩
        · rw [h, hzero] at ht
          exact Fin.succ_ne_zero v ht.symm
        · rw [h, hsucc] at ht
          exact hvr ⟨s, Fin.succ_inj.1 ht⟩
      · rintro ⟨w, hwr⟩
        have h0 : w ≠ 0 := by
          rintro rfl
          refine hwr ⟨0, ?_⟩
          have h : collapse j (k' + 1) hjk 0 = 0 := by
            rw [Fin.ext_iff, collapse_apply_val]
            simp
            omega
          dsimp only
          rw [h, hzero]
        obtain ⟨v, rfl⟩ := Fin.eq_succ_of_ne_zero h0
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

/-! ### (C) cocartesian cone edges are relatively initial -/

/-! #### Vertices and edges under `coneIso` -/

/-- The cone edge `(cone point) → 0` of `Δ[0] ⋆ Δ[n + 1]`. -/
abbrev coneEdge₀ (n : ℕ) : (cone (Δ[n + 1] : SSet.{u})).obj (op ⦋1⦌) :=
  ConeSimplex.cons (stdSimplex.vertex₀ n)

/-- `coneIso (n + 1)` sends the cone edge `coneEdge₀ n` to the edge `0 → 1` of `Δ[n + 2]`. -/
lemma coneIso_hom_coneEdge₀ (n : ℕ) :
    (stdSimplex.coneIso.{u} (n + 1)).hom.app (op ⦋1⦌) (coneEdge₀ n) =
      (horn.edge₀₁.{u} n).1 := by
  refine (stdSimplex.toConeFun_toUnderVertex₀ (n + 1) (coneEdge₀.{u} n)).trans ?_
  refine stdSimplex.ext _ _ fun i ↦ ?_
  fin_cases i <;> rfl

/-- The inverse form of `coneIso_hom_coneEdge₀`. -/
lemma coneIso_inv_edge₀₁ (n : ℕ) :
    (stdSimplex.coneIso.{u} (n + 1)).inv.app (op ⦋1⦌) (horn.edge₀₁.{u} n).1 = coneEdge₀ n := by
  rw [← coneIso_hom_coneEdge₀]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (stdSimplex.coneIso.{u} (n + 1)).hom_inv_id (op ⦋1⦌)) _

/-- Every vertex of `Δ[n + 1]`, in particular `0`, lies in `∂Δ[n + 1]`. -/
lemma vertex₀_mem_boundary (n : ℕ) :
    stdSimplex.vertex₀ n ∈ (boundary.{u} (n + 1)).obj (op ⦋0⦌) := by
  rw [boundary_obj_eq_univ 0 (n + 1)]
  trivial

/-- The vertex `0` of `∂Δ[n + 1]`. -/
abbrev boundaryVertex₀ (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.vertex₀ n, vertex₀_mem_boundary n⟩

/-- `coneIso n` sends the cone point to the vertex `0` (inverse form). -/
lemma coneIso_inv_vertex₀ (n : ℕ) :
    (stdSimplex.coneIso.{u} n).inv.app (op ⦋0⦌) (stdSimplex.vertex₀ n) =
      ConeSimplex.pt (Δ[n] : SSet.{u}) 0 := by
  have h : (stdSimplex.coneIso.{u} n).hom.app (op ⦋0⦌) (ConeSimplex.pt (Δ[n] : SSet.{u}) 0) =
      stdSimplex.vertex₀ n := by
    refine (stdSimplex.toConeFun_toUnderVertex₀ n (ConeSimplex.pt (Δ[n] : SSet.{u}) 0)).trans ?_
    refine stdSimplex.ext _ _ fun i ↦ ?_
    fin_cases i
    rfl
  rw [← h]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (stdSimplex.coneIso.{u} n).hom_inv_id (op ⦋0⦌)) _

/-! #### Transport of a lifting problem along `Subcomplex.preimageIso` -/

/-- A lifting problem for `A.preimage e.hom ↪ Y` has a solution as soon as the transported
problem for `A ↪ X` has one. -/
lemma Subcomplex.exists_lift_of_preimageIso {X Y E B : SSet.{u}} (A : X.Subcomplex) (e : Y ≅ X)
    (p : E ⟶ B) (a : (A.preimage e.hom : SSet.{u}) ⟶ E) (b : Y ⟶ B)
    (h : ∃ l : X ⟶ E, A.ι ≫ l = (A.preimageIso e).inv ≫ a ∧ l ≫ p = e.inv ≫ b) :
    ∃ l : Y ⟶ E, (A.preimage e.hom).ι ≫ l = a ∧ l ≫ p = b := by
  obtain ⟨l, hl₁, hl₂⟩ := h
  have he' : (A.preimage e.hom).ι ≫ e.hom = (A.preimageIso e).hom ≫ A.ι := rfl
  refine ⟨e.hom ≫ l, ?_, ?_⟩
  · rw [← Category.assoc, he', Category.assoc, hl₁, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hl₂, Iso.hom_inv_id_assoc]

/-- The commutative square of the transported lifting problem. -/
lemma Subcomplex.preimageIso_inv_comp_comp {X Y E B : SSet.{u}} (A : X.Subcomplex) (e : Y ≅ X)
    (p : E ⟶ B) (a : (A.preimage e.hom : SSet.{u}) ⟶ E) (b : Y ⟶ B)
    (w : a ≫ p = (A.preimage e.hom).ι ≫ b) :
    ((A.preimageIso e).inv ≫ a) ≫ p = A.ι ≫ e.inv ≫ b := by
  have he : (A.preimageIso e).inv ≫ (A.preimage e.hom).ι = A.ι ≫ e.inv := rfl
  rw [Category.assoc, w, ← Category.assoc, he, Category.assoc]

/-! #### The lifting problems -/

/-- The left horn problem `Λ[n + 2, 0] ↪ Δ[n + 2]` against `F`, in cone form: a lifting problem
for `A ↪ Δ[0] ⋆ Δ[n + 1]`, with `A` the preimage of `Λ[n + 2, 0]` under `coneIso (n + 1)`, whose
cone edge `coneEdge₀ n` goes to an `F`-cocartesian edge, has a solution. -/
lemma exists_lift_cone_of_isCocartesianEdge {C S : SSet.{u}} (F : C ⟶ S) (n : ℕ)
    (A : (cone (Δ[n + 1] : SSet.{u})).Subcomplex)
    (hA : A = Λ[n + 2, 0].preimage (stdSimplex.coneIso.{u} (n + 1)).hom)
    (u : (A : SSet.{u}) ⟶ C) (v : cone (Δ[n + 1] : SSet.{u}) ⟶ S) (w : u ≫ F = A.ι ≫ v)
    (hmem : coneEdge₀ n ∈ A.obj (op ⦋1⦌))
    (hedge : IsCocartesianEdge F (u.app (op ⦋1⦌) ⟨coneEdge₀ n, hmem⟩)) :
    ∃ l : cone (Δ[n + 1] : SSet.{u}) ⟶ C, A.ι ≫ l = u ∧ l ≫ F = v := by
  subst hA
  let e := Subcomplex.preimageIso Λ[n + 2, 0] (stdSimplex.coneIso.{u} (n + 1))
  refine Subcomplex.exists_lift_of_preimageIso _ _ F u v ?_
  have hσ : (e.inv ≫ u).app (op ⦋1⦌) (horn.edge₀₁ n) = u.app (op ⦋1⦌) ⟨coneEdge₀ n, hmem⟩ := by
    change u.app (op ⦋1⦌) (e.inv.app (op ⦋1⦌) (horn.edge₀₁ n)) = _
    congr 1
    exact Subtype.ext (coneIso_inv_edge₀₁ n)
  exact hedge.of_eq hσ.symm (e.inv ≫ u) _
    (Subcomplex.preimageIso_inv_comp_comp _ _ F u v w) rfl

/-- A boundary lifting problem for `∂Δ[n + 1] ↪ Δ[n + 1]` against `underMap F c` whose vertex `0`
goes to a vertex of `C_{c/}` with `F`-cocartesian cone edge has a solution. -/
lemma exists_lift_boundary_underMap {C S : SSet.{u}} (F : C ⟶ S) (c : C _⦋0⦌) (n : ℕ)
    (a : (∂Δ[n + 1] : SSet.{u}) ⟶ (C.under c : SSet.{u}))
    (b : Δ[n + 1] ⟶ (S.under (F.app _ c) : SSet.{u}))
    (w : a ≫ underMap F c = ∂Δ[n + 1].ι ≫ b)
    (hy : IsCocartesianEdge F (a.app (op ⦋0⦌) (boundaryVertex₀ n)).1) :
    ∃ l : Δ[n + 1] ⟶ (C.under c : SSet.{u}), ∂Δ[n + 1].ι ≫ l = a ∧ l ≫ underMap F c = b := by
  have hmem : coneEdge₀.{u} n ∈ (Subcomplex.cone ∂Δ[n + 1]).obj (op ⦋1⦌) :=
    vertex₀_mem_boundary n
  have hedge : IsCocartesianEdge F
      ((Subcomplex.coneLift ∂Δ[n + 1] ≫ toCone a).app (op ⦋1⦌) ⟨coneEdge₀ n, hmem⟩) := by
    refine hy.of_eq ?_
    change _ = C.map (SimplexCategory.mkHom (collapse 1 1 (n := 1) (by omega))).op
      (a.app (op ⦋0⦌) (boundaryVertex₀ n)).1
    rw [show SimplexCategory.mkHom (collapse 1 1 (n := 1) (by omega)) = 𝟙 _ from by
      ext i : 3
      exact Fin.ext (by change (i : ℕ) + 1 - 1 = (i : ℕ); omega)]
    rw [op_id, CategoryTheory.Functor.map_id_apply]
  exact exists_lift_underMap_of_cone F c _ a b
    (exists_lift_cone_of_isCocartesianEdge F n _ (cone_boundary_eq_preimage_horn (n + 1)) _ _
      (coneLift_toCone_comp F c _ a b w) hmem hedge)

/-- Transport along `coneIso n`: a cone-shaped lifting problem for a subcomplex `A` of
`Δ[0] ⋆ Δ[n]` which is the preimage of `∂Δ[n + 1]` is a boundary lifting problem for
`∂Δ[n + 1] ↪ Δ[n + 1]`, with the cone point becoming the vertex `0`. -/
lemma exists_lift_of_preimage_boundary {p : X ⟶ Y} {y : X _⦋0⦌} (n : ℕ)
    (h : ∀ (a : (∂Δ[n + 1] : SSet.{u}) ⟶ X) (b : Δ[n + 1] ⟶ Y), a ≫ p = ∂Δ[n + 1].ι ≫ b →
      a.app (op ⦋0⦌) (boundaryVertex₀ n) = y →
      ∃ l : Δ[n + 1] ⟶ X, ∂Δ[n + 1].ι ≫ l = a ∧ l ≫ p = b)
    (A : (cone (Δ[n] : SSet.{u})).Subcomplex)
    (hA : A = (boundary.{u} (n + 1)).preimage (stdSimplex.coneIso n).hom)
    (a : (A : SSet.{u}) ⟶ X) (b : cone (Δ[n] : SSet.{u}) ⟶ Y) (w : a ≫ p = A.ι ≫ b)
    (hmem : ConeSimplex.pt (Δ[n] : SSet.{u}) 0 ∈ A.obj (op ⦋0⦌))
    (hpt : a.app (op ⦋0⦌) ⟨ConeSimplex.pt _ 0, hmem⟩ = y) :
    ∃ l : cone (Δ[n] : SSet.{u}) ⟶ X, A.ι ≫ l = a ∧ l ≫ p = b := by
  subst hA
  let e := Subcomplex.preimageIso (boundary.{u} (n + 1)) (stdSimplex.coneIso.{u} n)
  refine Subcomplex.exists_lift_of_preimageIso _ _ p a b ?_
  have hv : (e.inv ≫ a).app (op ⦋0⦌) (boundaryVertex₀ n) = y := by
    rw [← hpt]
    change a.app (op ⦋0⦌) (e.inv.app (op ⦋0⦌) (boundaryVertex₀ n)) = _
    congr 1
  exact h _ _ (Subcomplex.preimageIso_inv_comp_comp _ _ p a b w) hv

/-- `HasConeLiftAt p y ∂Δ[n]` is the lifting property for `∂Δ[n + 1] ↪ Δ[n + 1]` against `p`
restricted to problems sending the vertex `0` to `y`. -/
lemma hasConeLiftAt_boundary_of_exists_lift {p : X ⟶ Y} {y : X _⦋0⦌} (n : ℕ)
    (h : ∀ (a : (∂Δ[n + 1] : SSet.{u}) ⟶ X) (b : Δ[n + 1] ⟶ Y), a ≫ p = ∂Δ[n + 1].ι ≫ b →
      a.app (op ⦋0⦌) (boundaryVertex₀ n) = y →
      ∃ l : Δ[n + 1] ⟶ X, ∂Δ[n + 1].ι ≫ l = a ∧ l ≫ p = b) :
    HasConeLiftAt p y (boundary.{u} n) := by
  intro a b w hpt
  have hmem : ConeSimplex.pt (Δ[n] : SSet.{u}) 0 ∈ (coneUnion (boundary.{u} n)).obj (op ⦋0⦌) :=
    Or.inl (Subcomplex.pt_mem_cone _ (op ⦋0⦌))
  refine exists_lift_of_preimage_boundary n h _ (coneUnion_boundary_eq_preimage n) a b w hmem ?_
  have := ConcreteCategory.congr_hom (NatTrans.congr_app hpt (op ⦋0⦌)) (stdSimplex.const 0 0 _)
  rw [const_app_zero_apply] at this
  exact this

/-- **(C)** If the cone edge `y.1 : c → y₁` of a vertex `y` of `C_{c/}` is `F`-cocartesian, then
`y` is `underMap F c`-initial. -/
theorem isRelInitial_underMap {C S : SSet.{u}} (F : C ⟶ S) (c : C _⦋0⦌)
    (y : (C.under c : SSet.{u}) _⦋0⦌) (hy : IsCocartesianEdge F y.1) :
    IsRelInitial (underMap F c) y := by
  intro n
  refine hasConeLiftAt_boundary_of_exists_lift n fun a b w ha ↦ ?_
  exact exists_lift_boundary_underMap F c n a b w (by rw [ha]; exact hy)

/-! ### (D) the full subcomplex of cocartesian cone edges -/

section UnderCocart

variable {C S : SSet.{u}}

/-- **(D)** The full subcomplex `C_{c/}^♮` of `C_{c/}` on the vertices whose cone edge is
`F`-cocartesian: an `n`-simplex belongs to it iff each of its vertices does. -/
def underCocart (F : C ⟶ S) (c : C _⦋0⦌) : (C.under c : SSet.{u}).Subcomplex where
  obj n := {x | ∀ i : Fin (n.unop.len + 1), IsCocartesianEdge F
    ((C.under c : SSet.{u}).map (SimplexCategory.const ⦋0⦌ n.unop i).op x).1}
  map {n m} f x hx i := by
    have h : IsCocartesianEdge F ((C.under c : SSet.{u}).map
        (SimplexCategory.const ⦋0⦌ n.unop (f.unop.toOrderHom i)).op x).1 := hx _
    have e : (C.under c : SSet.{u}).map
        (SimplexCategory.const ⦋0⦌ n.unop (f.unop.toOrderHom i)).op x =
        (C.under c : SSet.{u}).map (SimplexCategory.const ⦋0⦌ m.unop i).op
          ((C.under c : SSet.{u}).map f x) := by
      rw [← CategoryTheory.Functor.map_comp_apply]
      rfl
    rw [← e]
    exact @h

lemma mem_underCocart_iff (F : C ⟶ S) (c : C _⦋0⦌) {n : ℕ}
    (x : (C.under c : SSet.{u}) _⦋n⦌) :
    x ∈ (underCocart F c).obj (op ⦋n⦌) ↔ ∀ i : Fin (n + 1), IsCocartesianEdge F
      ((C.under c : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x).1 := Iff.rfl

lemma mem_underCocart_vertex_iff (F : C ⟶ S) (c : C _⦋0⦌) (y : (C.under c : SSet.{u}) _⦋0⦌) :
    y ∈ (underCocart F c).obj (op ⦋0⦌) ↔ IsCocartesianEdge F y.1 := by
  rw [mem_underCocart_iff]
  have e : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := SimplexCategory.Hom.ext_zero_left _ _
  constructor
  · intro h
    have h0 : IsCocartesianEdge F
        ((C.under c : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op y).1 := h 0
    rwa [e, op_id, CategoryTheory.Functor.map_id_apply] at h0
  · intro h i
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    rw [e, op_id, CategoryTheory.Functor.map_id_apply]
    exact h

end UnderCocart

/-! ### (E) `C_{c/}^♮ ⟶ S_{F c/}` is a trivial fibration -/

/-- **(E)** For a cocartesian fibration `F : C ⟶ S` and a vertex `c` of `C`, the restriction of
`underMap F c : C_{c/} ⟶ S_{F c/}` to the full subcomplex `underCocart F c` of cocartesian cone
edges is a trivial fibration: it has the right lifting property against all monomorphisms. -/
theorem rlp_monomorphisms_underCocart {C S : SSet.{u}} (F : C ⟶ S) [CocartesianFibration F]
    (c : C _⦋0⦌) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((underCocart F c).ι ≫ underMap F c) := by
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  constructor
  intro a b sq
  cases n with
  | zero =>
    -- a vertex of `S_{F c/}`, i.e. an edge `F c → s`, lifts to a cocartesian edge `c → x`
    obtain ⟨e, he₁, he₂, he₃⟩ := CocartesianFibration.exists_isCocartesianEdge F c
      (yonedaEquiv b).1 (by
        have h := (yonedaEquiv b).2
        change S.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op _ = _ at h
        rw [← SimplexCategory.δ_one_eq_const] at h
        exact h)
    let z : (C.under c : SSet.{u}) _⦋0⦌ := ⟨e, by
      change C.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op e = c
      rw [← SimplexCategory.δ_one_eq_const]
      exact he₁⟩
    have hz : z ∈ (underCocart F c).obj (op ⦋0⦌) :=
      (mem_underCocart_vertex_iff F c z).2 he₃
    refine ⟨⟨⟨yonedaEquiv.symm ⟨z, hz⟩, ?_, ?_⟩⟩⟩
    · -- `∂Δ[0]` is empty
      ext
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact Subtype.ext he₂
  | succ n =>
    have w : (a ≫ (underCocart F c).ι) ≫ underMap F c = ∂Δ[n + 1].ι ≫ b := by
      rw [Category.assoc]
      exact sq.w
    have hy : IsCocartesianEdge F
        ((a ≫ (underCocart F c).ι).app (op ⦋0⦌) (boundaryVertex₀ n)).1 :=
      (mem_underCocart_vertex_iff F c _).1 (a.app (op ⦋0⦌) (boundaryVertex₀ n)).2
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift_boundary_underMap F c n _ b w hy
    -- the lift lands in `underCocart F c`: its vertices are vertices of `∂Δ[n + 1]`
    have hrange : Subcomplex.range l ≤ underCocart F c := by
      rintro ⟨m⟩ _ ⟨z, rfl⟩
      intro i
      have hv : Δ[n + 1].map (SimplexCategory.const ⦋0⦌ m i).op z ∈
          (boundary.{u} (n + 1)).obj (op ⦋0⦌) := by
        rw [boundary_obj_eq_univ 0 (n + 1)]
        trivial
      have h1 : IsCocartesianEdge F ((a ≫ (underCocart F c).ι).app (op ⦋0⦌)
          ⟨Δ[n + 1].map (SimplexCategory.const ⦋0⦌ m i).op z, hv⟩).1 :=
        (mem_underCocart_vertex_iff F c _).1
          (a.app (op ⦋0⦌) ⟨Δ[n + 1].map (SimplexCategory.const ⦋0⦌ m i).op z, hv⟩).2
      have h2 : (a ≫ (underCocart F c).ι).app (op ⦋0⦌)
          ⟨Δ[n + 1].map (SimplexCategory.const ⦋0⦌ m i).op z, hv⟩ =
          (C.under c : SSet.{u}).map (SimplexCategory.const ⦋0⦌ m i).op (l.app (op m) z) := by
        rw [← hl₁, ← NatTrans.naturality_apply]
        rfl
      rw [h2] at h1
      exact @h1
    refine ⟨⟨⟨Subcomplex.lift l hrange, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono (underCocart F c).ι, Category.assoc, Subcomplex.lift_ι]
      exact hl₁
    · rw [← Category.assoc, Subcomplex.lift_ι]
      exact hl₂

end SSet
