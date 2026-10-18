/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.CosliceDiagram

/-!
# The slice of a simplicial set over a diagram

The mirror image of `Slice/CosliceDiagram.lean` in the *front* variable of the join: for a
diagram `b : B ⟶ X`,

`(X_{/b})_n = {F : Δ[n] ⋆ B ⟶ X // F` restricted to `B` is `b}`.

* `SSet.sliceDiag b` : the slice.
* `SSet.sliceDiagProj b : X_{/b} ⟶ X` : the projection.
* `SSet.sliceDiagRestrict v b : X_{/b} ⟶ X_{/(v ≫ b)}` : restriction along `v : B₀ ⟶ B`.
* `SSet.sliceDiagHomEquiv K b : (K ⟶ X_{/b}) ≃ {F : K ⋆ B ⟶ X // F|B = b}` : the universal
  property of the join in the front variable, with `SSet.sliceDiagToJoin` (whose combinatorial
  heart is `SSet.sliceDiagToJoinFun_map`) and `SSet.sliceDiagFromJoin`.

Why the mirror is wanted. The join-anodyne lemma gives an extension directly only when the front
factor is the boundary inclusion `∂Δ[p] ↪ Δ[p]` (`SSet.exists_join_extension_boundary`,
`Join/JoinExtension.lean`), while Kerodon 4.3.6.8 and 4.3.6.1
(`SSet.leftFibration_cosliceDiagRestrict`, `SSet.leftFibration_cosliceDiagProj`,
`Slice/SliceFibration.lean`) need an *arbitrary* monomorphism in the front factor. The slice
is exactly the adjoint that turns a statement about the front factor into a right lifting
property of a single morphism of simplicial sets, so that `SSet.rlp_monomorphisms` upgrades the
boundary case to all monomorphisms with no cell induction.
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

variable {K B X : SSet.{u}}

/-- An `n`-simplex of the slice `X_{/b}` over `b : B ⟶ X`: a morphism `Δ[n] ⋆ B ⟶ X`
restricting to `b` along `SSet.joinInr`. -/
abbrev SliceDiagSimplex (b : B ⟶ X) (n : SimplexCategoryᵒᵖ) : Type u :=
  {F : join (Δ[n.unop.len] : SSet.{u}) B ⟶ X // joinInr _ B ≫ F = b}

/-- The simplicial operator on `SSet.SliceDiagSimplex`: precomposition with `α ⋆ 𝟙_B`. -/
def sliceDiagMap (b : B ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : SliceDiagSimplex b n) : SliceDiagSimplex b m :=
  ⟨joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1, by
    rw [← Category.assoc, ← joinInr_naturality, Category.id_comp, F.2]⟩

@[simp]
lemma sliceDiagMap_coe (b : B ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : SliceDiagSimplex b n) :
    (sliceDiagMap b α F).1 = joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1 := rfl

/-- The slice `X_{/b}` over a diagram `b : B ⟶ X`. -/
def sliceDiag (b : B ⟶ X) : SSet.{u} where
  obj n := SliceDiagSimplex b n
  map α := ↾sliceDiagMap b α
  map_id n := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap (stdSimplex.map (𝟙 n.unop)) (𝟙 B) ≫ F.1 = F.1
    rw [CategoryTheory.Functor.map_id, joinMap_id, Category.id_comp])
  map_comp α β := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap (stdSimplex.map (α ≫ β).unop) (𝟙 B) ≫ F.1 =
      joinMap (stdSimplex.map β.unop) (𝟙 B) ≫ joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, ← CategoryTheory.Functor.map_comp]
    rfl)

@[simp]
lemma sliceDiag_map_coe (b : B ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : (sliceDiag b).obj n) :
    ((sliceDiag b).map α F).1 = joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1 := rfl

/-! ### From the join -/

/-- The morphism `K ⟶ X_{/b}` associated with a morphism `F : K ⋆ B ⟶ X` restricting to `b`
on the back block. -/
def sliceDiagFromJoin {b : B ⟶ X} (F : join K B ⟶ X) (hF : joinInr K B ≫ F = b) :
    K ⟶ sliceDiag b where
  app n := ↾fun y ↦ ⟨joinMap (yonedaEquiv.symm y) (𝟙 B) ≫ F, by
    rw [← Category.assoc, ← joinInr_naturality, Category.id_comp, hF]⟩
  naturality n m α := ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap (yonedaEquiv.symm (K.map α y)) (𝟙 B) ≫ F =
      joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ joinMap (yonedaEquiv.symm y) (𝟙 B) ≫ F
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, yonedaEquiv_symm_naturality_left]
    rfl)

@[simp]
lemma sliceDiagFromJoin_app_coe {b : B ⟶ X} (F : join K B ⟶ X) (hF : joinInr K B ≫ F = b)
    {n : SimplexCategoryᵒᵖ} (y : K.obj n) :
    ((sliceDiagFromJoin F hF).app n y).1 = joinMap (yonedaEquiv.symm y) (𝟙 B) ≫ F := rfl

/-! ### The projection and the restriction -/

/-- The projection `X_{/b} ⟶ X`: the front vertex block of `F : Δ[n] ⋆ B ⟶ X`. -/
def sliceDiagProj (b : B ⟶ X) : sliceDiag b ⟶ X where
  app n := ↾fun F ↦ yonedaEquiv (joinInl _ B ≫ F.1)
  naturality n m α := ConcreteCategory.hom_ext _ _ fun F ↦ by
    show yonedaEquiv (joinInl _ B ≫ joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1) =
      X.map α.unop.op (yonedaEquiv (joinInl _ B ≫ F.1))
    rw [yonedaEquiv_naturality, ← Category.assoc, ← joinInl_naturality, Category.assoc]

@[simp]
lemma sliceDiagProj_app (b : B ⟶ X) {n : SimplexCategoryᵒᵖ} (F : (sliceDiag b).obj n) :
    (sliceDiagProj b).app n F = yonedaEquiv (joinInl _ B ≫ F.1) := rfl

/-- Restriction of the slice along `v : B₀ ⟶ B`. -/
def sliceDiagRestrict {B₀ : SSet.{u}} (v : B₀ ⟶ B) (b : B ⟶ X) :
    sliceDiag b ⟶ sliceDiag (v ≫ b) where
  app n := ↾fun F ↦ ⟨joinMap (𝟙 _) v ≫ F.1, by
    rw [← Category.assoc, ← joinInr_naturality, Category.assoc, F.2]⟩
  naturality n m α := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap (𝟙 _) v ≫ joinMap (stdSimplex.map α.unop) (𝟙 B) ≫ F.1 =
      joinMap (stdSimplex.map α.unop) (𝟙 B₀) ≫ joinMap (𝟙 _) v ≫ F.1
    rw [← Category.assoc, ← Category.assoc, ← joinMap_comp, ← joinMap_comp, Category.comp_id,
      Category.id_comp, Category.comp_id, Category.id_comp])

@[simp]
lemma sliceDiagRestrict_app_coe {B₀ : SSet.{u}} (v : B₀ ⟶ B) (b : B ⟶ X)
    {n : SimplexCategoryᵒᵖ} (F : (sliceDiag b).obj n) :
    ((sliceDiagRestrict v b).app n F).1 = joinMap (𝟙 _) v ≫ F.1 := rfl

/-! ### To the join -/

variable {b : B ⟶ X}

/-- The `q`-simplex of `X` attached by `φ : K ⟶ X_{/b}` to the components of a `q`-simplex of
`K ⋆ B`: on the block `j = 0` it is the diagram `b`, on `j = j' + 1` it is the morphism
`Δ[j'] ⋆ B ⟶ X` classified by `φ`, evaluated at the simplex whose front block is the identity. -/
def sliceDiagToJoinFun (φ : K ⟶ sliceDiag b) :
    ∀ {q j k : ℕ}, j + k = q + 1 → K.aug j → B.aug k → X _⦋q⦌
  | q, 0, k, hjk, _, y =>
      b.app (op ⦋q⦌) (B.augMap (finCastHom (a := q + 1) (b := k) (by omega)) y)
  | q, (j + 1), k, hjk, x, y =>
      (φ.app (op ⦋j⦌) x).1.app (op ⦋q⦌) ⟨j + 1, k, hjk, idAug j, y⟩

lemma sliceDiagToJoinFun_zero (φ : K ⟶ sliceDiag b) {q k : ℕ} (hjk : 0 + k = q + 1)
    (x : K.aug 0) (y : B.aug k) (h : q + 1 = k) :
    sliceDiagToJoinFun φ hjk x y = b.app (op ⦋q⦌) (B.augMap (finCastHom h) y) := rfl

lemma sliceDiagToJoinFun_succ (φ : K ⟶ sliceDiag b) {q j k : ℕ} (hjk : (j + 1) + k = q + 1)
    (x : K.aug (j + 1)) (y : B.aug k) :
    sliceDiagToJoinFun φ hjk x y =
      (φ.app (op ⦋j⦌) x).1.app (op ⦋q⦌) ⟨j + 1, k, hjk, idAug j, y⟩ := rfl

lemma sliceDiagToJoinFun_congr (φ : K ⟶ sliceDiag b) {q j j' k : ℕ}
    (hjk : j + k = q + 1) (hjk' : j' + k = q + 1)
    {x : K.aug j} {x' : K.aug j'} (hx : HEq x x') (y : B.aug k) :
    sliceDiagToJoinFun φ hjk x y = sliceDiagToJoinFun φ hjk' x' y := by
  obtain rfl : j = j' := by omega
  rw [eq_of_heq hx]

/-- The compatibility of `SSet.sliceDiagToJoinFun` with reindexing. -/
lemma sliceDiagToJoinFun_map (φ : K ⟶ sliceDiag b) {q q' j k : ℕ} (hjk : j + k = q + 1)
    (x : K.aug j) (y : B.aug k) (ρ : Fin (q' + 1) →o Fin (q + 1))
    (h' : cut ρ j + (q' + 1 - cut ρ j) = q' + 1) :
    sliceDiagToJoinFun φ h' (K.augMap (initialSeg ρ j) x) (B.augMap (residual ρ j k hjk) y) =
      X.map (mkHom ρ).op (sliceDiagToJoinFun φ hjk x y) := by
  have hcle : cut ρ j ≤ q' + 1 := cut_le ρ j
  cases j with
  | zero =>
    have hc : cut ρ 0 = 0 := cut_zero ρ
    have h₀ : 0 + (q' + 1 - cut ρ 0) = q' + 1 := by omega
    have h₁ : q' + 1 = q' + 1 - cut ρ 0 := by omega
    have h₂ : q + 1 = k := by omega
    refine Eq.trans (sliceDiagToJoinFun_congr φ h' h₀ (aug_heq_unit (by omega) _) _) ?_
    show b.app (op ⦋q'⦌) (B.augMap (finCastHom h₁) (B.augMap (residual ρ 0 k hjk) y)) =
      X.map (mkHom ρ).op (b.app (op ⦋q⦌) (B.augMap (finCastHom h₂) y))
    refine Eq.trans ?_ (NatTrans.naturality_apply b (mkHom ρ).op _)
    refine congrArg (b.app (op ⦋q'⦌)) ?_
    show B.augMap (finCastHom h₁) (B.augMap (residual ρ 0 k hjk) y) =
      B.augMap ρ (B.augMap (finCastHom h₂) y)
    rw [← augMap_comp, ← augMap_comp]
    exact congrArg (fun σ : Fin (q' + 1) →o Fin k ↦ B.augMap σ y)
      (OrderHom.ext _ _ (funext fun i ↦ Fin.ext
        (residual_zero_val ρ k hjk _ i rfl)))
  | succ j' =>
    rcases Nat.eq_zero_or_pos (cut ρ (j' + 1)) with hb | hpos
    · have h₀ : 0 + (q' + 1 - cut ρ (j' + 1)) = q' + 1 := by omega
      have h₁ : q' + 1 = q' + 1 - cut ρ (j' + 1) := by omega
      refine Eq.trans (sliceDiagToJoinFun_congr φ h' h₀ (aug_heq_unit hb _) _) ?_
      show b.app (op ⦋q'⦌)
          (B.augMap (finCastHom h₁) (B.augMap (residual ρ (j' + 1) k hjk) y)) =
        X.map (mkHom ρ).op
          ((φ.app (op ⦋j'⦌) x).1.app (op ⦋q⦌) ⟨j' + 1, k, hjk, idAug j', y⟩)
      refine Eq.trans ?_ (NatTrans.naturality_apply (φ.app (op ⦋j'⦌) x).1 (mkHom ρ).op _)
      have hinr : (⟨j' + 1, k, hjk, idAug j', y⟩ :
            JoinSimplex (Δ[j'] : SSet.{u}) B q).map ρ =
          JoinSimplex.inr (B.augMap (finCastHom h₁)
            (B.augMap (residual ρ (j' + 1) k hjk) y)) :=
        JoinSimplex.ext_of_j_eq (by show cut ρ (j' + 1) = 0; omega)
          (aug_heq_unit (by show cut ρ (j' + 1) = 0; omega) _)
          (HEq.symm (augMap_finCastHom_heq _ _))
      refine Eq.trans ?_ (congrArg ((φ.app (op ⦋j'⦌) x).1.app (op ⦋q'⦌)) hinr.symm)
      have hbw : ∀ w : B _⦋q'⦌, b.app (op ⦋q'⦌) w =
          (φ.app (op ⦋j'⦌) x).1.app (op ⦋q'⦌) (JoinSimplex.inr w) := fun w ↦
        (congrArg (fun F : B ⟶ X ↦ F.app (op ⦋q'⦌) w) (φ.app (op ⦋j'⦌) x).2).symm
      exact hbw _
    · obtain ⟨j'', hb⟩ : ∃ j'', cut ρ (j' + 1) = j'' + 1 := ⟨cut ρ (j' + 1) - 1, by omega⟩
      have h₂ : (j'' + 1) + (q' + 1 - cut ρ (j' + 1)) = q' + 1 := by omega
      set τ := initialSeg ρ (j' + 1) with hτ
      have hx : HEq (K.augMap τ x) (K.augMap (τ.comp (finCastHom hb.symm)) x) := by
        rw [augMap_comp]
        exact (augMap_finCastHom_heq hb.symm _).symm
      refine Eq.trans (sliceDiagToJoinFun_congr φ h' h₂ hx _) ?_
      show (φ.app (op ⦋j''⦌) (K.augMap (τ.comp (finCastHom hb.symm)) x)).1.app (op ⦋q'⦌)
          ⟨j'' + 1, q' + 1 - cut ρ (j' + 1), h₂, idAug j'',
            B.augMap (residual ρ (j' + 1) k hjk) y⟩ =
        X.map (mkHom ρ).op
          ((φ.app (op ⦋j'⦌) x).1.app (op ⦋q⦌) ⟨j' + 1, k, hjk, idAug j', y⟩)
      have hφ : φ.app (op ⦋j''⦌) (K.augMap (τ.comp (finCastHom hb.symm)) x) =
          (sliceDiag b).map (mkHom (τ.comp (finCastHom hb.symm))).op (φ.app (op ⦋j'⦌) x) :=
        NatTrans.naturality_apply φ (mkHom (τ.comp (finCastHom hb.symm))).op x
      refine Eq.trans (congrArg (fun z : (sliceDiag b).obj (op ⦋j''⦌) ↦
        z.1.app (op ⦋q'⦌) ⟨j'' + 1, q' + 1 - cut ρ (j' + 1), h₂, idAug j'',
          B.augMap (residual ρ (j' + 1) k hjk) y⟩) hφ) ?_
      refine Eq.trans ?_ (NatTrans.naturality_apply (φ.app (op ⦋j'⦌) x).1 (mkHom ρ).op _)
      show (φ.app (op ⦋j'⦌) x).1.app (op ⦋q'⦌)
          (JoinSimplex.mapHom (stdSimplex.map (mkHom (τ.comp (finCastHom hb.symm)))) (𝟙 B)
            ⟨j'' + 1, q' + 1 - cut ρ (j' + 1), h₂, idAug j'',
              B.augMap (residual ρ (j' + 1) k hjk) y⟩) = _
      refine congrArg ((φ.app (op ⦋j'⦌) x).1.app (op ⦋q'⦌)) ?_
      refine JoinSimplex.ext_of_j_eq hb.symm ?_ (heq_of_eq (augHom_id _))
      show HEq (augHom (stdSimplex.map (mkHom (τ.comp (finCastHom hb.symm)))) (idAug j''))
        ((Δ[j'] : SSet.{u}).augMap τ (idAug j'))
      rw [augHom_stdSimplex_map_idAug]
      refine stdSimplex.aug_heq_of_augVal hb.symm _ _ fun i hi ↦ ?_
      rw [stdSimplex.augVal_augOfOrderHom _ hi, stdSimplex.augVal_augMap _ _ (by omega),
        augVal_idAug _ (by omega)]
      rfl

lemma sliceDiagToJoinFun_inr (φ : K ⟶ sliceDiag b) {q : ℕ} (y : B _⦋q⦌) :
    sliceDiagToJoinFun φ (JoinSimplex.inr (A := K) y).hjk (JoinSimplex.inr (A := K) y).x
      (JoinSimplex.inr (A := K) y).y = b.app (op ⦋q⦌) y :=
  congrArg (fun w : B _⦋q⦌ ↦ b.app (op ⦋q⦌) w) (B.augMap_id (q + 1) y)

/-- The morphism `K ⋆ B ⟶ X` associated with `φ : K ⟶ X_{/b}`. -/
def sliceDiagToJoin (φ : K ⟶ sliceDiag b) : join K B ⟶ X where
  app _ := ↾fun s ↦ sliceDiagToJoinFun φ s.hjk s.x s.y
  naturality _ _ ρ := ConcreteCategory.hom_ext _ _ fun s ↦
    sliceDiagToJoinFun_map φ s.hjk s.x s.y ρ.unop.toOrderHom (s.map ρ.unop.toOrderHom).hjk

@[simp]
lemma sliceDiagToJoin_app (φ : K ⟶ sliceDiag b) {n : SimplexCategoryᵒᵖ}
    (s : (join K B).obj n) :
    (sliceDiagToJoin φ).app n s = sliceDiagToJoinFun φ s.hjk s.x s.y := rfl

/-- The back block of `SSet.sliceDiagToJoin` is the diagram `b`. -/
lemma joinInr_comp_sliceDiagToJoin (φ : K ⟶ sliceDiag b) :
    joinInr K B ≫ sliceDiagToJoin φ = b :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun y ↦ sliceDiagToJoinFun_inr φ y)

lemma sliceDiagToJoin_sliceDiagFromJoin (F : join K B ⟶ X) (hF : joinInr K B ≫ F = b) :
    sliceDiagToJoin (sliceDiagFromJoin F hF) = F := by
  ext n s
  obtain ⟨j, k, hjk, x, y⟩ := s
  cases j with
  | zero =>
    obtain rfl : k = n.unop.len + 1 := by omega
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app hF n) y
    show b.app n (B.augMap (finCastHom rfl) y) = _
    refine Eq.trans (congrArg (fun w : B _⦋n.unop.len⦌ ↦ b.app n w) (B.augMap_id _ y)) h1.symm
  | succ j' =>
    show F.app n (JoinSimplex.mapHom (yonedaEquiv.symm x) (𝟙 B)
        ⟨j' + 1, k, hjk, idAug j', y⟩) = _
    exact congrArg (fun t : (join K B).obj n ↦ F.app n t)
      (JoinSimplex.ext_of_j_eq rfl (heq_of_eq (augHom_yonedaEquiv_symm_idAug x))
        (heq_of_eq (augHom_id y)))

lemma sliceDiagFromJoin_sliceDiagToJoin (φ : K ⟶ sliceDiag b) :
    sliceDiagFromJoin (sliceDiagToJoin φ) (joinInr_comp_sliceDiagToJoin φ) = φ := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_)
  ext m s
  obtain ⟨j, k, hjk, z, y⟩ := s
  cases j with
  | zero =>
    obtain rfl : k = m.unop.len + 1 := by omega
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (φ.app n x).2 m) y
    show b.app m (B.augMap (finCastHom rfl) (augHom (𝟙 B) y)) = _
    refine Eq.trans (congrArg (fun w : B _⦋m.unop.len⦌ ↦ b.app m w) ?_) h1.symm
    rw [augHom_id]
    exact B.augMap_id _ y
  | succ j'' =>
    have hφ : φ.app (op ⦋j''⦌) (augHom (yonedaEquiv.symm x) z) =
        (sliceDiag b).map (stdSimplex.objEquiv z).op (φ.app n x) :=
      NatTrans.naturality_apply φ (stdSimplex.objEquiv z).op x
    have hzz : ∀ w : (Δ[(unop n).len] : SSet.{u}) _⦋j''⦌,
        augHom (stdSimplex.map (stdSimplex.objEquiv w)) (idAug.{u} j'') = w := fun w ↦
      (augHom_stdSimplex_map_idAug (stdSimplex.objEquiv w).toOrderHom).trans
        (stdSimplex.augOfOrderHom_augOrderHom (m := (unop n).len) (j := j'' + 1) w)
    have hyy : augHom (𝟙 B) (augHom (𝟙 B) y) = y := by rw [augHom_id, augHom_id]
    refine Eq.trans (congrArg (fun w : (sliceDiag b).obj (op ⦋j''⦌) ↦
      w.1.app m ⟨j'' + 1, k, hjk, idAug j'', augHom (𝟙 B) y⟩) hφ) ?_
    show (φ.app n x).1.app m (JoinSimplex.mapHom (stdSimplex.map (stdSimplex.objEquiv z)) (𝟙 B)
        ⟨j'' + 1, k, hjk, idAug j'', augHom (𝟙 B) y⟩) = _
    exact congrArg (fun t : (join (Δ[n.unop.len] : SSet.{u}) B).obj m ↦ (φ.app n x).1.app m t)
      (JoinSimplex.ext_of_j_eq rfl (heq_of_eq (hzz z)) (heq_of_eq hyy))

/-- The universal property of the join in the front variable: morphisms `K ⟶ X_{/b}` are
morphisms `K ⋆ B ⟶ X` restricting to the diagram `b` on `B`. -/
@[simps]
def sliceDiagHomEquiv (K : SSet.{u}) (b : B ⟶ X) :
    (K ⟶ sliceDiag b) ≃ {F : join K B ⟶ X // joinInr K B ≫ F = b} where
  toFun φ := ⟨sliceDiagToJoin φ, joinInr_comp_sliceDiagToJoin φ⟩
  invFun F := sliceDiagFromJoin F.1 F.2
  left_inv φ := sliceDiagFromJoin_sliceDiagToJoin φ
  right_inv F := Subtype.ext (sliceDiagToJoin_sliceDiagFromJoin F.1 F.2)

/-! ### Naturality of the universal property -/

/-- Naturality of `sliceDiagFromJoin` in the shape. -/
lemma sliceDiagFromJoin_naturality {K' : SSet.{u}} (v : K' ⟶ K) (F : join K B ⟶ X)
    (hF : joinInr K B ≫ F = b) :
    v ≫ sliceDiagFromJoin F hF =
      sliceDiagFromJoin (joinMap v (𝟙 B) ≫ F)
        (by rw [← Category.assoc, ← joinInr_naturality, Category.id_comp, hF]) :=
  NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap (yonedaEquiv.symm (v.app n y)) (𝟙 B) ≫ F =
      joinMap (yonedaEquiv.symm y) (𝟙 B) ≫ joinMap v (𝟙 B) ≫ F
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, yonedaEquiv_symm_comp]))

/-- Naturality of `sliceDiagFromJoin` in the diagram: restricting along `v : B₀ ⟶ B`. -/
lemma sliceDiagFromJoin_restrict {B₀ : SSet.{u}} (v : B₀ ⟶ B) (F : join K B ⟶ X)
    (hF : joinInr K B ≫ F = b) :
    sliceDiagFromJoin F hF ≫ sliceDiagRestrict v b =
      sliceDiagFromJoin (joinMap (𝟙 K) v ≫ F)
        (by rw [← Category.assoc, ← joinInr_naturality, Category.assoc, hF]) :=
  NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap (𝟙 _) v ≫ joinMap (yonedaEquiv.symm y) (𝟙 B) ≫ F =
      joinMap (yonedaEquiv.symm y) (𝟙 B₀) ≫ joinMap (𝟙 K) v ≫ F
    rw [← Category.assoc, ← Category.assoc, ← joinMap_comp, ← joinMap_comp, Category.comp_id,
      Category.id_comp, Category.comp_id, Category.id_comp]))

/-- `sliceDiagFromJoin` depends only on the map out of the join, not on the proof that it
restricts to `b`. -/
lemma sliceDiagFromJoin_congr {b : B ⟶ X} {F F' : join K B ⟶ X} (h : F = F')
    (hF : joinInr K B ≫ F = b) (hF' : joinInr K B ≫ F' = b) :
    sliceDiagFromJoin F hF = sliceDiagFromJoin F' hF' := by
  subst h; rfl

/-- Naturality of `sliceDiagToJoin` in the shape. -/
lemma sliceDiagToJoin_naturality {K' : SSet.{u}} (v : K' ⟶ K) (φ : K ⟶ sliceDiag b) :
    sliceDiagToJoin (v ≫ φ) = joinMap v (𝟙 B) ≫ sliceDiagToJoin φ := by
  conv_lhs => rw [← sliceDiagFromJoin_sliceDiagToJoin φ, sliceDiagFromJoin_naturality]
  rw [sliceDiagToJoin_sliceDiagFromJoin]

/-- Naturality of `sliceDiagToJoin` in the diagram: restricting along `v : B₀ ⟶ B`. -/
lemma sliceDiagToJoin_restrict {B₀ : SSet.{u}} (v : B₀ ⟶ B) (φ : K ⟶ sliceDiag b) :
    sliceDiagToJoin (φ ≫ sliceDiagRestrict v b) = joinMap (𝟙 K) v ≫ sliceDiagToJoin φ := by
  conv_lhs => rw [← sliceDiagFromJoin_sliceDiagToJoin φ, sliceDiagFromJoin_restrict]
  rw [sliceDiagToJoin_sliceDiagFromJoin]

end SSet
