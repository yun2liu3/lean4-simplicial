/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.Fiber
import SimplicialHomotopy.Anodyne.Deformation
import SimplicialHomotopy.Anodyne.RightAnodyne
import SimplicialHomotopy.Equivalence.WeakEquivalence
import SimplicialHomotopy.Slice.Undercategory

/-!
# The fiber `E_c` as a deformation retract of `E ×_C C_{c/}`

For a right fibration `q : E ⟶ C` and a vertex `c` of `C`, the fiber `E_c = fiber q c` sits
inside the pullback `E ×_C C_{c/}` over the vertex `id_c` of the undercategory `C_{c/}`
(`SSet.under C c`, defined by décalage in `SimplicialHomotopy.Slice.Undercategory`). We show that
this inclusion is a strong deformation retract, hence a homotopy equivalence; in particular
weak contractibility of `E ×_C C_{c/}` implies weak contractibility of `E_c` (step 3 of the
assembly in `Cofinal/TheoremA.lean`).

The argument is the one of [Lur09, proof of 4.1.3.1]: the undercategory `C_{c/}` contracts
onto `id_c` (`SSet.underContraction`: an `m`-simplex `x : Δ[m + 1] ⟶ C` with cone point `c`
and a time `t : ⦋m⦌ ⟶ ⦋1⦌` are sent to `x ∘ θ t` where `θ t` keeps the vertices `j + 1` with
`t j = 1` and collapses the others onto the cone point). Since `E ×_C C_{c/} ⟶ C_{c/}` is a
right fibration, the contraction lifts along the right anodyne inclusion
`(E_c ⊗ Δ[1]) ∪ (E ×_C C_{c/} ⊗ {1}) ↪ E ×_C C_{c/} ⊗ Δ[1]`, starting from the identity at
time `1` and the constant homotopy on `E_c`; the time-`0` end of the lift is a retraction onto
`E_c`.

## Main declarations

* `SimplexCategory.contractHom t` : the map `θ t : ⦋m + 1⦌ ⟶ ⦋m + 1⦌` above, and its
  compatibility with `SimplexCategory.coneShiftHom`.
* `SSet.underContraction c : C_{c/} ⊗ Δ[1] ⟶ C_{c/}`, with `SSet.ι₁_underContraction`,
  `SSet.ι₀_underContraction`, `SSet.const_underId_whiskerRight_underContraction`.
* `SSet.fiberToPullbackUnder q c : fiber q c ⟶ pullback q (C.underProj c)`, a monomorphism.
* `SSet.exists_retraction_fiberToPullbackUnder` : `E_c` is a strong deformation retract of
  `E ×_C C_{c/}`; `SSet.isHomotopyEquivalence_fiberToPullbackUnder`.
* `SSet.weaklyContractible_fiber_of_pullback_under` : weak contractibility of `E ×_C C_{c/}`
  implies that of `E_c`.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

open scoped Simplicial

namespace SimplexCategory

/-- The map `Fin (m + 2) → Fin (m + 2)` fixing `0`, fixing `j.succ` when `t j = 1` and sending
it to `0` otherwise. -/
def contractOrderHom {m : ℕ} (t : Fin (m + 1) →o Fin 2) : Fin (m + 2) →o Fin (m + 2) where
  toFun := Fin.cases 0 (fun j ↦ if t j = 1 then j.succ else 0)
  monotone' := by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        simp only [Fin.cases_succ]
        have hle := t.monotone (Fin.succ_le_succ_iff.1 hij)
        have key : ∀ a b : Fin 2, a ≤ b → a = 1 → b = 1 := by decide
        split_ifs with hi hj hj
        · exact hij
        · exact (hj (key _ _ hle hi)).elim
        · exact Fin.zero_le _
        · exact le_rfl

@[simp]
lemma contractOrderHom_zero {m : ℕ} (t : Fin (m + 1) →o Fin 2) : contractOrderHom t 0 = 0 := rfl

@[simp]
lemma contractOrderHom_succ {m : ℕ} (t : Fin (m + 1) →o Fin 2) (j : Fin (m + 1)) :
    contractOrderHom t j.succ = if t j = 1 then j.succ else 0 := rfl

/-- The contraction map `θ t : ⦋m + 1⦌ ⟶ ⦋m + 1⦌` attached to `t : ⦋m⦌ ⟶ ⦋1⦌`: it fixes the
cone point `0`, fixes `j + 1` when `t j = 1` and sends it to the cone point otherwise. -/
def contractHom {m : SimplexCategory} (t : m ⟶ ⦋1⦌) : ⦋m.len + 1⦌ ⟶ ⦋m.len + 1⦌ :=
  mkHom (contractOrderHom t.toOrderHom)

/-- `θ t` fixes the cone point. -/
lemma const_zero_comp_contractHom {m : SimplexCategory} (t : m ⟶ ⦋1⦌) :
    const ⦋0⦌ ⦋m.len + 1⦌ 0 ≫ contractHom t = const ⦋0⦌ ⦋m.len + 1⦌ 0 := by
  ext i : 3
  rfl

/-- `θ` is natural with respect to `coneShiftHom`. -/
lemma coneShiftHom_comp_contractHom {m n : SimplexCategory} (f : m ⟶ n) (t : n ⟶ ⦋1⦌) :
    coneShiftHom f ≫ contractHom t = contractHom (f ≫ t) ≫ coneShiftHom f := by
  ext i : 3
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [contractHom, coneShiftHom, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      OrderHom.comp_coe, Function.comp_apply, coneShiftFun_succ, contractOrderHom_succ]
    split_ifs <;> rfl

/-- At time `1`, `θ` is the identity. -/
lemma contractHom_eq_id {m : SimplexCategory} (t : m ⟶ ⦋1⦌) (ht : ∀ j, t.toOrderHom j = 1) :
    contractHom t = 𝟙 _ := by
  ext i : 3
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [contractHom, mkHom, Hom.toOrderHom_mk, contractOrderHom_succ, ht, ite_true]
    rfl

/-- At time `0`, `θ` is the constant map at the cone point. -/
lemma contractHom_eq_const {m : SimplexCategory} (t : m ⟶ ⦋1⦌) (ht : ∀ j, t.toOrderHom j = 0) :
    contractHom t = const ⦋m.len + 1⦌ ⦋m.len + 1⦌ 0 := by
  ext i : 3
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [contractHom, mkHom, Hom.toOrderHom_mk, contractOrderHom_succ, ht, const_apply]
    rfl

end SimplexCategory

namespace SSet

section

variable {C : SSet.{u}} (c : C _⦋0⦌)

/-- Two simplices of `C` obtained from a vertex `z` by maps to `⦋0⦌` agree. -/
lemma map_op_apply_eq_of_to_zero {k : SimplexCategory} (g g' : k ⟶ ⦋0⦌) (z : C _⦋0⦌) :
    C.map g.op z = C.map g'.op z := by
  rw [Subsingleton.elim g g']

/-! ### The contraction of `C_{c/}` onto `id_c` -/

/-- The contraction of `C_{c/}` onto the vertex `id_c`: at time `1` the identity, at time `0`
the constant map at `id_c`. -/
noncomputable def underContraction :
    (C.under c : SSet.{u}) ⊗ Δ[1] ⟶ (C.under c : SSet.{u}) where
  app m := ↾fun x ↦ ⟨C.map (SimplexCategory.contractHom (stdSimplex.objEquiv x.2)).op x.1.1, by
    change C.decVertex _ = c
    dsimp only [decVertex]
    rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_zero_comp_contractHom]
    exact x.1.2⟩
  naturality m n f := ConcreteCategory.hom_ext _ _ fun ⟨⟨x, hx⟩, t⟩ ↦ Subtype.ext (by
    change C.map (SimplexCategory.contractHom (f.unop ≫ stdSimplex.objEquiv t)).op
      (C.map (SimplexCategory.coneShiftHom f.unop).op x) =
      C.map (SimplexCategory.coneShiftHom f.unop).op
        (C.map (SimplexCategory.contractHom (stdSimplex.objEquiv t)).op x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      SimplexCategory.coneShiftHom_comp_contractHom])

lemma underContraction_app_val {m : SimplexCategoryᵒᵖ}
    (x : ((C.under c : SSet.{u}) ⊗ Δ[1]).obj m) :
    ((underContraction c).app m x).1 =
      C.map (SimplexCategory.contractHom (stdSimplex.objEquiv x.2)).op x.1.1 := rfl

lemma const_app_val {Y : SSet.{u}} (y : (C.under c : SSet.{u}) _⦋0⦌) {m : SimplexCategoryᵒᵖ}
    (z : Y.obj m) :
    ((const y : Y ⟶ (C.under c : SSet.{u})).app m z).1 =
      C.map (SimplexCategory.coneShiftHom (m.unop.const ⦋0⦌ 0)).op y.1 := rfl

lemma ι₁_underContraction : ι₁ ≫ underContraction c = 𝟙 _ := by
  ext m ⟨x, hx⟩
  apply Subtype.ext
  change C.map (SimplexCategory.contractHom _).op x = x
  rw [SimplexCategory.contractHom_eq_id _ (fun _ ↦ rfl), op_id, Functor.map_id_apply]

lemma ι₀_underContraction : ι₀ ≫ underContraction c = const (C.underId c) := by
  ext m ⟨x, hx⟩
  apply Subtype.ext
  change C.map (SimplexCategory.contractHom _).op x =
    C.map (SimplexCategory.coneShiftHom (m.unop.const ⦋0⦌ 0)).op (C.map (SimplexCategory.σ 0).op c)
  rw [SimplexCategory.contractHom_eq_const _ (fun _ ↦ rfl), SimplexCategory.const_fac_thru_zero,
    op_comp, Functor.map_comp_apply]
  change C.map _ (C.decVertex x) = _
  rw [hx, ← Functor.map_comp_apply, ← op_comp]
  exact map_op_apply_eq_of_to_zero _ _ _

lemma const_underId_whiskerRight_underContraction {Y : SSet.{u}} :
    (const (C.underId c) : Y ⟶ (C.under c : SSet.{u})) ▷ Δ[1] ≫ underContraction c =
      CartesianMonoidalCategory.fst _ _ ≫ const (C.underId c) := by
  ext m ⟨y, t⟩
  apply Subtype.ext
  change C.map (SimplexCategory.contractHom _).op
      (C.map (SimplexCategory.coneShiftHom (m.unop.const ⦋0⦌ 0)).op
        (C.map (SimplexCategory.σ 0).op c)) =
    C.map (SimplexCategory.coneShiftHom (m.unop.const ⦋0⦌ 0)).op (C.map (SimplexCategory.σ 0).op c)
  simp only [← Functor.map_comp_apply, ← op_comp]
  exact map_op_apply_eq_of_to_zero _ _ _

lemma underProj_app_underId : (C.underProj c).app _ (C.underId c) = c := by
  change C.map (SimplexCategory.δ 0).op (C.map (SimplexCategory.σ 0).op c) = c
  rw [← Functor.map_comp_apply, ← op_comp,
    Subsingleton.elim (SimplexCategory.δ 0 ≫ SimplexCategory.σ 0) (𝟙 _), op_id,
    Functor.map_id_apply]

lemma const_underId_comp_underProj {Y : SSet.{u}} :
    (const (C.underId c) : Y ⟶ _) ≫ C.underProj c = const c := by
  rw [const_comp, underProj_app_underId]

/-! ### The vertex `{1}` of `Δ[1]` -/

/-- `ι₁ : X ⟶ X ⊗ Δ[1]` factors through `X ⊗ {1}`. -/
lemma ι₁_eq_toProdPt_comp (X : SSet.{u}) :
    (ι₁ : X ⟶ X ⊗ Δ[1]) = toProdPt X ≫ X ◁ (stdSimplex.faceSingletonIso (1 : Fin 2)).hom ≫
      X ◁ (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  rw [← MonoidalCategory.whiskerLeft_comp, stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ,
    stdSimplex.δ_zero_eq_const, whiskerLeft_const_one, toProdPt_fst_assoc]

end

/-! ### The fiber inside `E ×_C C_{c/}` -/

section

variable {C E : SSet.{u}} (q : E ⟶ C) (c : C _⦋0⦌)

/-- The fiber `E_c` inside `E ×_C C_{c/}`, over the vertex `id_c`. -/
noncomputable def fiberToPullbackUnder : fiber q c ⟶ pullback q (C.underProj c) :=
  pullback.lift (fiberι q c) (const (C.underId c))
    (by rw [fiberι_comp_eq_const, const_underId_comp_underProj])

@[reassoc (attr := simp)]
lemma fiberToPullbackUnder_fst : fiberToPullbackUnder q c ≫ pullback.fst _ _ = fiberι q c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fiberToPullbackUnder_snd :
    fiberToPullbackUnder q c ≫ pullback.snd _ _ = const (C.underId c) :=
  pullback.lift_snd _ _ _

instance : Mono (fiberToPullbackUnder q c) := mono_of_mono_fac (fiberToPullbackUnder_fst q c)

lemma range_fiberToPullbackUnder_ι_comp_snd :
    (Subcomplex.range (fiberToPullbackUnder q c)).ι ≫ pullback.snd q (C.underProj c) =
      const (C.underId c) := by
  have h : (Subcomplex.range (fiberToPullbackUnder q c)).ι =
      inv (Subcomplex.toRange (fiberToPullbackUnder q c)) ≫ fiberToPullbackUnder q c := by
    rw [IsIso.eq_inv_comp, Subcomplex.toRange_ι]
  rw [h, Category.assoc, fiberToPullbackUnder_snd, comp_const]

variable [RightFibration q]

instance : RightFibration (pullback.snd q (C.underProj c)) :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback q (C.underProj c))
    (mem_rightFibrations q)⟩

/-- The contraction of `C_{c/}` lifts to `E ×_C C_{c/}`, starting from the identity at time `1`
and constant on the fiber `E_c`. -/
lemma exists_underDeformation :
    ∃ G : pullback q (C.underProj c) ⊗ Δ[1] ⟶ pullback q (C.underProj c),
      ι₁ ≫ G = 𝟙 _ ∧
      fiberToPullbackUnder q c ▷ Δ[1] ≫ G = fst _ _ ≫ fiberToPullbackUnder q c ∧
      G ≫ pullback.snd q (C.underProj c) =
        pullback.snd q (C.underProj c) ▷ Δ[1] ≫ underContraction c := by
  -- the inclusion `(E_c ⊗ Δ[1]) ∪ (P ⊗ {1}) ↪ P ⊗ Δ[1]` is right anodyne
  have hB : rightAnodyneExtensions (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
    rw [← horn_one_one_eq_face]
    exact rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1)
  have hlift := rightAnodyneExtensions_unionProd_ι (Subcomplex.range (fiberToPullbackUnder q c))
    _ hB _ (mem_rightFibrations (pullback.snd q (C.underProj c)))
  -- the map on the union: identity at time `1`, constant homotopy on `E_c`
  have hglue : (Subcomplex.range (fiberToPullbackUnder q c)).ι ▷
        ((stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫ fst _ _ =
      (Subcomplex.range (fiberToPullbackUnder q c) : SSet.{u}) ◁
        (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι ≫ fst _ _ ≫
          (Subcomplex.range (fiberToPullbackUnder q c)).ι := by
    rw [whiskerRight_fst, whiskerLeft_fst_assoc]
  obtain ⟨top, htop₁, htop₂⟩ : ∃ top : ((Subcomplex.range (fiberToPullbackUnder q c)).unionProd
        (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
          pullback q (C.underProj c),
      Subcomplex.unionProd.ι₁ _ _ ≫ top = fst _ _ ∧
      Subcomplex.unionProd.ι₂ _ _ ≫ top =
        fst _ _ ≫ (Subcomplex.range (fiberToPullbackUnder q c)).ι :=
    ⟨(Subcomplex.unionProd.isPushout _ _).desc _ _ hglue,
      (Subcomplex.unionProd.isPushout _ _).inl_desc _ _ _,
      (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _⟩
  -- the lifting square
  have sq : CommSq top ((Subcomplex.range (fiberToPullbackUnder q c)).unionProd
      (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι (pullback.snd q (C.underProj c))
      (pullback.snd q (C.underProj c) ▷ Δ[1] ≫ underContraction c) := ⟨by
    apply (Subcomplex.unionProd.isPushout _ _).hom_ext
    · rw [reassoc_of% htop₁, Subcomplex.unionProd.ι₁_ι_assoc, whisker_exchange_assoc,
        whiskerLeft_face_one_ι, Category.assoc, ι₁_underContraction, Category.comp_id,
        whiskerRight_fst]
    · rw [reassoc_of% htop₂, Subcomplex.unionProd.ι₂_ι_assoc, ← comp_whiskerRight_assoc,
        range_fiberToPullbackUnder_ι_comp_snd, const_underId_whiskerRight_underContraction]⟩
  obtain ⟨G, hG, hG'⟩ : ∃ G : pullback q (C.underProj c) ⊗ Δ[1] ⟶ pullback q (C.underProj c),
      ((Subcomplex.range (fiberToPullbackUnder q c)).unionProd
        (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫ G = top ∧
      G ≫ pullback.snd q (C.underProj c) =
        pullback.snd q (C.underProj c) ▷ Δ[1] ≫ underContraction c :=
    ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  refine ⟨G, ?_, ?_, hG'⟩
  · rw [ι₁_eq_toProdPt_comp, Category.assoc, Category.assoc, ← Subcomplex.unionProd.ι₁_ι_assoc,
      hG, htop₁, whiskerLeft_fst, toProdPt_fst]
  · rw [← Subcomplex.toRange_ι (fiberToPullbackUnder q c), comp_whiskerRight, Category.assoc,
      ← Subcomplex.unionProd.ι₂_ι_assoc, hG, htop₂, whiskerRight_fst_assoc]

/-- `E_c` is a strong deformation retract of `E ×_C C_{c/}`. -/
theorem exists_retraction_fiberToPullbackUnder :
    ∃ r : pullback q (C.underProj c) ⟶ fiber q c, fiberToPullbackUnder q c ≫ r = 𝟙 _ ∧
      Nonempty (Homotopy (r ≫ fiberToPullbackUnder q c) (𝟙 _)) := by
  obtain ⟨G, hG₁, hGj, hGsnd⟩ := exists_underDeformation q c
  -- the time-`0` end of `G` lands in the fiber
  have h₀ : (ι₀ ≫ G) ≫ pullback.snd q (C.underProj c) = const (C.underId c) := by
    rw [Category.assoc, hGsnd, ι₀_comp_assoc, ι₀_underContraction, comp_const]
  let r : pullback q (C.underProj c) ⟶ fiber q c :=
    pullback.lift ((ι₀ ≫ G) ≫ pullback.fst q (C.underProj c)) (toUnit _) (by
      rw [comp_const, Category.assoc, pullback.condition, ← Category.assoc, h₀,
        const_underId_comp_underProj])
  have hr : r ≫ fiberToPullbackUnder q c = ι₀ ≫ G := by
    apply pullback.hom_ext
    · rw [Category.assoc, fiberToPullbackUnder_fst]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, fiberToPullbackUnder_snd, comp_const, h₀]
  refine ⟨r, ?_, ⟨Homotopy.mk' G hr.symm hG₁⟩⟩
  rw [← cancel_mono (fiberToPullbackUnder q c), Category.assoc, hr, Category.id_comp,
    ← ι₀_comp_assoc, hGj, ι₀_fst_assoc]

/-- For a right fibration `q`, the inclusion `E_c ⟶ E ×_C C_{c/}` of the fiber is a homotopy
equivalence; a homotopy inverse is the retraction of `exists_retraction_fiberToPullbackUnder`. -/
theorem isHomotopyEquivalence_fiberToPullbackUnder :
    IsHomotopyEquivalence (fiberToPullbackUnder q c) := by
  obtain ⟨r, hr, H⟩ := exists_retraction_fiberToPullbackUnder q c
  exact ⟨r, ⟨(Homotopy.refl' _).ofEq' hr.symm rfl⟩, H⟩

/-- If `E ×_C C_{c/}` is weakly contractible then so is the fiber `E_c`. -/
theorem weaklyContractible_fiber_of_pullback_under
    (h : WeaklyContractible (pullback q (C.underProj c))) : WeaklyContractible (fiber q c) :=
  weaklyContractible_of_isWeakHomotopyEquivalence (fiberToPullbackUnder q c)
    (isHomotopyEquivalence_fiberToPullbackUnder q c).isWeakHomotopyEquivalence h

end

end SSet
