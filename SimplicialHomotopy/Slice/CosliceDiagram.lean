/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.CosliceJoin

/-!
# The coslice of a simplicial set under a diagram

Kerodon Tag 017Y (`X_{g/}` for an arbitrary `g : L ⟶ X`). `Slice/Coslice.lean` builds the
coslice under a *simplex* by the décalage; that model is computational but it cannot express
Kerodon 4.3.6.8, where the diagram is the boundary `∂Δ[p] ⟶ X`. Here the coslice is defined by
Kerodon's own formula, through the join of `Join/Join.lean`:

`(X_{g/})_n = {F : L ⋆ Δ[n] ⟶ X // F` restricted to `L` is `g}`.

* `SSet.cosliceDiag g` : the coslice.
* `SSet.cosliceDiagProj g : X_{g/} ⟶ X` : the projection.
* `SSet.cosliceDiagRestrict u g : X_{g/} ⟶ X_{(u ≫ g)/}` : restriction along `u : L₀ ⟶ L`.
* `SSet.cosliceDiagHomEquiv K g : (K ⟶ X_{g/}) ≃ {F : L ⋆ K ⟶ X // F|L = g}` : the universal
  property of the join (Kerodon Tag 0189), with the two constructions `SSet.cosliceDiagToJoin`
  (whose combinatorial heart is `SSet.cosliceDiagToJoinFun_map`) and `SSet.cosliceDiagFromJoin`.

Unlike the décalage model, this coslice is defined for a diagram of *any* shape `L`, which is
what Kerodon 4.3.6.8 (and hence Proposition 4.4.2.13, Tag 01H0) needs: there `L = ∂Δ[p]`.
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

variable {K L X : SSet.{u}}

/-- An `n`-simplex of the coslice `X_{g/}` under `g : L ⟶ X`: a morphism `L ⋆ Δ[n] ⟶ X`
restricting to `g` along `SSet.joinInl`. -/
abbrev CosliceDiagSimplex (g : L ⟶ X) (n : SimplexCategoryᵒᵖ) : Type u :=
  {F : join L (Δ[n.unop.len] : SSet.{u}) ⟶ X // joinInl L _ ≫ F = g}

/-- The simplicial operator on `SSet.CosliceDiagSimplex`: precomposition with `𝟙_L ⋆ α`. -/
def cosliceDiagMap (g : L ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : CosliceDiagSimplex g n) : CosliceDiagSimplex g m :=
  ⟨joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1, by
    rw [← Category.assoc, ← joinInl_naturality, Category.id_comp, F.2]⟩

@[simp]
lemma cosliceDiagMap_coe (g : L ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : CosliceDiagSimplex g n) :
    (cosliceDiagMap g α F).1 = joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1 := rfl

/-- The coslice `X_{g/}` under a diagram `g : L ⟶ X` (Kerodon 017Y). -/
def cosliceDiag (g : L ⟶ X) : SSet.{u} where
  obj n := CosliceDiagSimplex g n
  map α := ↾cosliceDiagMap g α
  map_id n := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap (𝟙 L) (stdSimplex.map (𝟙 n.unop)) ≫ F.1 = F.1
    rw [CategoryTheory.Functor.map_id, joinMap_id, Category.id_comp])
  map_comp α β := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap (𝟙 L) (stdSimplex.map (α ≫ β).unop) ≫ F.1 =
      joinMap (𝟙 L) (stdSimplex.map β.unop) ≫ joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, ← CategoryTheory.Functor.map_comp]
    rfl)

@[simp]
lemma cosliceDiag_map_coe (g : L ⟶ X) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (F : (cosliceDiag g).obj n) :
    ((cosliceDiag g).map α F).1 = joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1 := rfl

/-! ### From the join -/

/-- The morphism `K ⟶ X_{g/}` associated with a morphism `F : L ⋆ K ⟶ X` restricting to `g`
on the front block. -/
def cosliceDiagFromJoin {g : L ⟶ X} (F : join L K ⟶ X) (hF : joinInl L K ≫ F = g) :
    K ⟶ cosliceDiag g where
  app n := ↾fun y ↦ ⟨joinMap (𝟙 L) (yonedaEquiv.symm y) ≫ F, by
    rw [← Category.assoc, ← joinInl_naturality, Category.id_comp, hF]⟩
  naturality n m α := ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap (𝟙 L) (yonedaEquiv.symm (K.map α y)) ≫ F =
      joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ joinMap (𝟙 L) (yonedaEquiv.symm y) ≫ F
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, yonedaEquiv_symm_naturality_left]
    rfl)

@[simp]
lemma cosliceDiagFromJoin_app_coe {g : L ⟶ X} (F : join L K ⟶ X) (hF : joinInl L K ≫ F = g)
    {n : SimplexCategoryᵒᵖ} (y : K.obj n) :
    ((cosliceDiagFromJoin F hF).app n y).1 = joinMap (𝟙 L) (yonedaEquiv.symm y) ≫ F := rfl

/-! ### The projection and the restriction -/

/-- The projection `X_{g/} ⟶ X`: the back vertex block of `F : L ⋆ Δ[n] ⟶ X`. -/
def cosliceDiagProj (g : L ⟶ X) : cosliceDiag g ⟶ X where
  app n := ↾fun F ↦ yonedaEquiv (joinInr L _ ≫ F.1)
  naturality n m α := ConcreteCategory.hom_ext _ _ fun F ↦ by
    show yonedaEquiv (joinInr L _ ≫ joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1) =
      X.map α.unop.op (yonedaEquiv (joinInr L _ ≫ F.1))
    rw [yonedaEquiv_naturality, ← Category.assoc, ← joinInr_naturality, Category.assoc]

@[simp]
lemma cosliceDiagProj_app (g : L ⟶ X) {n : SimplexCategoryᵒᵖ} (F : (cosliceDiag g).obj n) :
    (cosliceDiagProj g).app n F = yonedaEquiv (joinInr L _ ≫ F.1) := rfl

/-- Restriction of the coslice along `u : L₀ ⟶ L`. -/
def cosliceDiagRestrict {L₀ : SSet.{u}} (u : L₀ ⟶ L) (g : L ⟶ X) :
    cosliceDiag g ⟶ cosliceDiag (u ≫ g) where
  app n := ↾fun F ↦ ⟨joinMap u (𝟙 _) ≫ F.1, by
    rw [← Category.assoc, ← joinInl_naturality, Category.assoc, F.2]⟩
  naturality n m α := ConcreteCategory.hom_ext _ _ fun F ↦ Subtype.ext (by
    show joinMap u (𝟙 _) ≫ joinMap (𝟙 L) (stdSimplex.map α.unop) ≫ F.1 =
      joinMap (𝟙 L₀) (stdSimplex.map α.unop) ≫ joinMap u (𝟙 _) ≫ F.1
    rw [← Category.assoc, ← Category.assoc, ← joinMap_comp, ← joinMap_comp, Category.comp_id,
      Category.id_comp, Category.comp_id, Category.id_comp])

@[simp]
lemma cosliceDiagRestrict_app_coe {L₀ : SSet.{u}} (u : L₀ ⟶ L) (g : L ⟶ X)
    {n : SimplexCategoryᵒᵖ} (F : (cosliceDiag g).obj n) :
    ((cosliceDiagRestrict u g).app n F).1 = joinMap u (𝟙 _) ≫ F.1 := rfl

/-! ### To the join -/

/-- The monotone map `Fin a →o Fin b` given by an equality of degrees; the underlying map of
`Fin.castOrderIso`. -/
def finCastHom {a b : ℕ} (h : a = b) : Fin a →o Fin b :=
  (Fin.castOrderIso h).toOrderEmbedding.toOrderHom

@[simp]
lemma finCastHom_apply_val {a b : ℕ} (h : a = b) (i : Fin a) : (finCastHom h i : ℕ) = i := rfl

lemma finCastHom_rfl (a : ℕ) : finCastHom (rfl : a = a) = OrderHom.id := rfl

variable {g : L ⟶ X}

/-- The `q`-simplex of `X` attached by `φ : K ⟶ X_{g/}` to the components of a `q`-simplex of
`L ⋆ K`: on the block `k = 0` it is the diagram `g`, on `k = k' + 1` it is the morphism
`L ⋆ Δ[k'] ⟶ X` classified by `φ`, evaluated at the simplex whose back block is the identity. -/
def cosliceDiagToJoinFun (φ : K ⟶ cosliceDiag g) :
    ∀ {q j k : ℕ}, j + k = q + 1 → L.aug j → K.aug k → X _⦋q⦌
  | q, _, 0, hjk, x, _ => g.app (op ⦋q⦌) (L.augMap (finCastHom hjk.symm) x)
  | q, j, (k + 1), hjk, x, y =>
      (φ.app (op ⦋k⦌) y).1.app (op ⦋q⦌) ⟨j, k + 1, hjk, x, idAug k⟩

lemma cosliceDiagToJoinFun_zero (φ : K ⟶ cosliceDiag g) {q j : ℕ} (hjk : j + 0 = q + 1)
    (x : L.aug j) (y : K.aug 0) :
    cosliceDiagToJoinFun φ hjk x y = g.app (op ⦋q⦌) (L.augMap (finCastHom hjk.symm) x) := rfl

lemma cosliceDiagToJoinFun_succ (φ : K ⟶ cosliceDiag g) {q j k : ℕ} (hjk : j + (k + 1) = q + 1)
    (x : L.aug j) (y : K.aug (k + 1)) :
    cosliceDiagToJoinFun φ hjk x y =
      (φ.app (op ⦋k⦌) y).1.app (op ⦋q⦌) ⟨j, k + 1, hjk, x, idAug k⟩ := rfl

lemma augMap_finCastHom_heq {A : SSet.{u}} {a b : ℕ} (h : a = b) (z : A.aug b) :
    HEq (A.augMap (finCastHom h) z) z := by
  subst h
  exact heq_of_eq (A.augMap_id _ _)

lemma aug_heq_unit {A : SSet.{u}} {d : ℕ} (h : d = 0) (z : A.aug d) :
    HEq z (PUnit.unit : A.aug 0) := by
  subst h
  exact heq_of_eq rfl

lemma cosliceDiagToJoinFun_congr (φ : K ⟶ cosliceDiag g) {q j k k' : ℕ}
    (hjk : j + k = q + 1) (hjk' : j + k' = q + 1) (x : L.aug j)
    {y : K.aug k} {y' : K.aug k'} (hy : HEq y y') :
    cosliceDiagToJoinFun φ hjk x y = cosliceDiagToJoinFun φ hjk' x y' := by
  obtain rfl : k = k' := by omega
  rw [eq_of_heq hy]

/-- The back block of the join: the identity simplex of `Δ[a]` pushed along `τ` is the simplex
of `Δ[k]` classified by `τ`. -/
lemma augHom_stdSimplex_map_idAug {a k : ℕ} (τ : Fin (a + 1) →o Fin (k + 1)) :
    augHom (stdSimplex.map (mkHom τ)) (idAug.{u} a) = stdSimplex.augOfOrderHom τ := rfl

/-- The compatibility of `SSet.cosliceDiagToJoinFun` with reindexing. -/
lemma cosliceDiagToJoinFun_map (φ : K ⟶ cosliceDiag g) {q q' j k : ℕ} (hjk : j + k = q + 1)
    (x : L.aug j) (y : K.aug k) (ρ : Fin (q' + 1) →o Fin (q + 1))
    (h' : cut ρ j + (q' + 1 - cut ρ j) = q' + 1) :
    cosliceDiagToJoinFun φ h' (L.augMap (initialSeg ρ j) x) (K.augMap (residual ρ j k hjk) y) =
      X.map (mkHom ρ).op (cosliceDiagToJoinFun φ hjk x y) := by
  have hcle : cut ρ j ≤ q' + 1 := cut_le ρ j
  cases k with
  | zero =>
    have hj : j = q + 1 := by omega
    subst hj
    have hc : cut ρ (q + 1) = q' + 1 := cut_top ρ
    have h₀ : cut ρ (q + 1) + 0 = q' + 1 := by omega
    refine Eq.trans (cosliceDiagToJoinFun_congr φ h' h₀ _ (aug_heq_unit (by omega) _)) ?_
    show g.app (op ⦋q'⦌) (L.augMap (finCastHom h₀.symm) (L.augMap (initialSeg ρ (q + 1)) x)) =
      X.map (mkHom ρ).op (g.app (op ⦋q⦌) (L.augMap (finCastHom hjk.symm) x))
    refine Eq.trans ?_ (NatTrans.naturality_apply g (mkHom ρ).op _)
    refine congrArg (g.app (op ⦋q'⦌)) ?_
    show L.augMap (finCastHom h₀.symm) (L.augMap (initialSeg ρ (q + 1)) x) =
      L.augMap ρ (L.augMap (finCastHom hjk.symm) x)
    rw [← augMap_comp, ← augMap_comp]
    exact congrArg (fun σ : Fin (q' + 1) →o Fin (q + 1 + 0) ↦ L.augMap σ x)
      (OrderHom.ext _ _ (funext fun i ↦ Fin.ext
        (initialSeg_top_val ρ (finCastHom h₀.symm i) ⟨i, i.isLt⟩ rfl)))
  | succ k' =>
    rcases Nat.eq_zero_or_pos (q' + 1 - cut ρ j) with hb | hpos
    · have h₀ : cut ρ j + 0 = q' + 1 := by omega
      refine Eq.trans (cosliceDiagToJoinFun_congr φ h' h₀ _ (aug_heq_unit hb _)) ?_
      show g.app (op ⦋q'⦌) (L.augMap (finCastHom h₀.symm) (L.augMap (initialSeg ρ j) x)) =
        X.map (mkHom ρ).op ((φ.app (op ⦋k'⦌) y).1.app (op ⦋q⦌) ⟨j, k' + 1, hjk, x, idAug k'⟩)
      refine Eq.trans ?_
        (NatTrans.naturality_apply (φ.app (op ⦋k'⦌) y).1 (mkHom ρ).op _)
      have hinl : (⟨j, k' + 1, hjk, x, idAug k'⟩ : JoinSimplex L (Δ[k'] : SSet.{u}) q).map ρ =
          JoinSimplex.inl (L.augMap (finCastHom h₀.symm) (L.augMap (initialSeg ρ j) x)) :=
        JoinSimplex.ext_of_j_eq (by show cut ρ j = q' + 1; omega)
          (HEq.symm (augMap_finCastHom_heq h₀.symm _))
          (aug_heq_unit (by show q' + 1 - cut ρ j = 0; omega) _)
      refine Eq.trans ?_ (congrArg ((φ.app (op ⦋k'⦌) y).1.app (op ⦋q'⦌)) hinl.symm)
      have hgw : ∀ w : L _⦋q'⦌, g.app (op ⦋q'⦌) w =
          (φ.app (op ⦋k'⦌) y).1.app (op ⦋q'⦌) (JoinSimplex.inl w) := fun w ↦
        (congrArg (fun F : L ⟶ X ↦ F.app (op ⦋q'⦌) w) (φ.app (op ⦋k'⦌) y).2).symm
      exact hgw _
    · obtain ⟨k'', hb⟩ : ∃ k'', q' + 1 - cut ρ j = k'' + 1 := ⟨q' - cut ρ j, by omega⟩
      have h₂ : cut ρ j + (k'' + 1) = q' + 1 := by omega
      set τ := residual ρ j (k' + 1) hjk with hτ
      have hy : HEq (K.augMap τ y) (K.augMap (τ.comp (finCastHom hb.symm)) y) := by
        rw [augMap_comp]
        exact (augMap_finCastHom_heq hb.symm _).symm
      refine Eq.trans (cosliceDiagToJoinFun_congr φ h' h₂ _ hy) ?_
      show (φ.app (op ⦋k''⦌) (K.augMap (τ.comp (finCastHom hb.symm)) y)).1.app (op ⦋q'⦌)
          ⟨cut ρ j, k'' + 1, h₂, L.augMap (initialSeg ρ j) x, idAug k''⟩ =
        X.map (mkHom ρ).op ((φ.app (op ⦋k'⦌) y).1.app (op ⦋q⦌) ⟨j, k' + 1, hjk, x, idAug k'⟩)
      have hφ : φ.app (op ⦋k''⦌) (K.augMap (τ.comp (finCastHom hb.symm)) y) =
          (cosliceDiag g).map (mkHom (τ.comp (finCastHom hb.symm))).op (φ.app (op ⦋k'⦌) y) :=
        NatTrans.naturality_apply φ (mkHom (τ.comp (finCastHom hb.symm))).op y
      refine Eq.trans (congrArg (fun z : (cosliceDiag g).obj (op ⦋k''⦌) ↦
        z.1.app (op ⦋q'⦌) ⟨cut ρ j, k'' + 1, h₂, L.augMap (initialSeg ρ j) x, idAug k''⟩) hφ) ?_
      refine Eq.trans ?_ (NatTrans.naturality_apply (φ.app (op ⦋k'⦌) y).1 (mkHom ρ).op _)
      show (φ.app (op ⦋k'⦌) y).1.app (op ⦋q'⦌)
          (JoinSimplex.mapHom (𝟙 L) (stdSimplex.map (mkHom (τ.comp (finCastHom hb.symm))))
            ⟨cut ρ j, k'' + 1, h₂, L.augMap (initialSeg ρ j) x, idAug k''⟩) = _
      refine congrArg ((φ.app (op ⦋k'⦌) y).1.app (op ⦋q'⦌)) ?_
      refine JoinSimplex.ext_of_j_eq rfl (heq_of_eq (augHom_id _)) ?_
      show HEq (augHom (stdSimplex.map (mkHom (τ.comp (finCastHom hb.symm)))) (idAug k''))
        ((Δ[k'] : SSet.{u}).augMap τ (idAug k'))
      rw [augHom_stdSimplex_map_idAug]
      refine stdSimplex.aug_heq_of_augVal hb.symm _ _ fun i hi ↦ ?_
      rw [stdSimplex.augVal_augOfOrderHom _ hi, stdSimplex.augVal_augMap _ _ (by omega),
        augVal_idAug _ (by omega)]
      rfl

lemma cosliceDiagToJoinFun_inl (φ : K ⟶ cosliceDiag g) {q : ℕ} (x : L _⦋q⦌) :
    cosliceDiagToJoinFun φ (JoinSimplex.inl (B := K) x).hjk (JoinSimplex.inl (B := K) x).x
      (JoinSimplex.inl (B := K) x).y = g.app (op ⦋q⦌) x :=
  congrArg (fun w : L _⦋q⦌ ↦ g.app (op ⦋q⦌) w) (L.augMap_id (q + 1) x)

/-- The morphism `L ⋆ K ⟶ X` associated with `φ : K ⟶ X_{g/}`. -/
def cosliceDiagToJoin (φ : K ⟶ cosliceDiag g) : join L K ⟶ X where
  app _ := ↾fun s ↦ cosliceDiagToJoinFun φ s.hjk s.x s.y
  naturality _ _ ρ := ConcreteCategory.hom_ext _ _ fun s ↦
    cosliceDiagToJoinFun_map φ s.hjk s.x s.y ρ.unop.toOrderHom (s.map ρ.unop.toOrderHom).hjk

@[simp]
lemma cosliceDiagToJoin_app (φ : K ⟶ cosliceDiag g) {n : SimplexCategoryᵒᵖ}
    (s : (join L K).obj n) :
    (cosliceDiagToJoin φ).app n s = cosliceDiagToJoinFun φ s.hjk s.x s.y := rfl

/-- The front block of `SSet.cosliceDiagToJoin` is the diagram `g`. -/
lemma joinInl_comp_cosliceDiagToJoin (φ : K ⟶ cosliceDiag g) :
    joinInl L K ≫ cosliceDiagToJoin φ = g :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ cosliceDiagToJoinFun_inl φ x)

lemma augHom_yonedaEquiv_symm_idAug {k : ℕ} (y : K _⦋k⦌) :
    augHom (yonedaEquiv.symm y) (idAug.{u} k) = y := by
  show (yonedaEquiv.symm y).app (op ⦋k⦌) (idAug.{u} k) = y
  rw [show (idAug.{u} k : (Δ[k] : SSet.{u}) _⦋k⦌) = stdSimplex.objEquiv.symm (𝟙 ⦋k⦌) from rfl,
    yonedaEquiv_symm_app_objEquiv_symm, op_id, Functor.map_id_apply]

lemma cosliceDiagToJoin_cosliceDiagFromJoin (F : join L K ⟶ X) (hF : joinInl L K ≫ F = g) :
    cosliceDiagToJoin (cosliceDiagFromJoin F hF) = F := by
  ext n s
  obtain ⟨j, k, hjk, x, y⟩ := s
  cases k with
  | zero =>
    obtain rfl : j = n.unop.len + 1 := by omega
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app hF n) x
    show g.app n (L.augMap (finCastHom hjk.symm) x) = _
    refine Eq.trans (congrArg (fun w : L _⦋n.unop.len⦌ ↦ g.app n w) (L.augMap_id _ x)) h1.symm
  | succ k' =>
    show F.app n (JoinSimplex.mapHom (𝟙 L) (yonedaEquiv.symm y)
        ⟨j, k' + 1, hjk, x, idAug k'⟩) = _
    exact congrArg (fun t : (join L K).obj n ↦ F.app n t)
      (JoinSimplex.ext_of_j_eq rfl (heq_of_eq (augHom_id x))
        (heq_of_eq (augHom_yonedaEquiv_symm_idAug y)))

lemma cosliceDiagFromJoin_cosliceDiagToJoin (φ : K ⟶ cosliceDiag g) :
    cosliceDiagFromJoin (cosliceDiagToJoin φ) (joinInl_comp_cosliceDiagToJoin φ) = φ := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext ?_)
  ext m s
  obtain ⟨j, k, hjk, x, z⟩ := s
  cases k with
  | zero =>
    obtain rfl : j = m.unop.len + 1 := by omega
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (φ.app n y).2 m) x
    show g.app m (L.augMap (finCastHom hjk.symm) (augHom (𝟙 L) x)) = _
    refine Eq.trans (congrArg (fun w : L _⦋m.unop.len⦌ ↦ g.app m w) ?_) h1.symm
    rw [augHom_id]
    exact L.augMap_id _ x
  | succ k'' =>
    have hφ : φ.app (op ⦋k''⦌) (augHom (yonedaEquiv.symm y) z) =
        (cosliceDiag g).map (stdSimplex.objEquiv z).op (φ.app n y) :=
      NatTrans.naturality_apply φ (stdSimplex.objEquiv z).op y
    have hzz : ∀ w : (Δ[(unop n).len] : SSet.{u}) _⦋k''⦌,
        augHom (stdSimplex.map (stdSimplex.objEquiv w)) (idAug.{u} k'') = w := fun w ↦
      (augHom_stdSimplex_map_idAug (stdSimplex.objEquiv w).toOrderHom).trans
        (stdSimplex.augOfOrderHom_augOrderHom (m := (unop n).len) (j := k'' + 1) w)
    have hxx : augHom (𝟙 L) (augHom (𝟙 L) x) = x := by rw [augHom_id, augHom_id]
    refine Eq.trans (congrArg (fun w : (cosliceDiag g).obj (op ⦋k''⦌) ↦
      w.1.app m ⟨j, k'' + 1, hjk, augHom (𝟙 L) x, idAug k''⟩) hφ) ?_
    show (φ.app n y).1.app m (JoinSimplex.mapHom (𝟙 L) (stdSimplex.map (stdSimplex.objEquiv z))
        ⟨j, k'' + 1, hjk, augHom (𝟙 L) x, idAug k''⟩) = _
    exact congrArg (fun t : (join L (Δ[n.unop.len] : SSet.{u})).obj m ↦ (φ.app n y).1.app m t)
      (JoinSimplex.ext_of_j_eq rfl (heq_of_eq hxx) (heq_of_eq (hzz z)))

/-- (U1) The universal property of the join: morphisms `K ⟶ X_{g/}` are morphisms
`L ⋆ K ⟶ X` restricting to the diagram `g` on `L` (Kerodon Tag 0189). -/
@[simps]
def cosliceDiagHomEquiv (K : SSet.{u}) (g : L ⟶ X) :
    (K ⟶ cosliceDiag g) ≃ {F : join L K ⟶ X // joinInl L K ≫ F = g} where
  toFun φ := ⟨cosliceDiagToJoin φ, joinInl_comp_cosliceDiagToJoin φ⟩
  invFun F := cosliceDiagFromJoin F.1 F.2
  left_inv φ := cosliceDiagFromJoin_cosliceDiagToJoin φ
  right_inv F := Subtype.ext (cosliceDiagToJoin_cosliceDiagFromJoin F.1 F.2)

/-! ### Naturality of the universal property

`cosliceDiagHomEquiv` is natural in the shape `K` and in the diagram: precomposing a morphism
`K' ⟶ K` corresponds to `joinMap (𝟙 L) v`, and restricting the diagram along `u : L₀ ⟶ L`
corresponds to `joinMap u (𝟙 K)`. Both are formal for `cosliceDiagFromJoin` and are transported
to `cosliceDiagToJoin` through the two round trips. They are what turns a lifting problem for
`X_{g/} ⟶ X_{(u ≫ g)/}` into a lifting problem inside the join. -/

/-- Naturality of `cosliceDiagFromJoin` in the shape. -/
lemma cosliceDiagFromJoin_naturality {K' : SSet.{u}} (v : K' ⟶ K) (F : join L K ⟶ X)
    (hF : joinInl L K ≫ F = g) :
    v ≫ cosliceDiagFromJoin F hF =
      cosliceDiagFromJoin (joinMap (𝟙 L) v ≫ F)
        (by rw [← Category.assoc, ← joinInl_naturality, Category.id_comp, hF]) :=
  NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap (𝟙 L) (yonedaEquiv.symm (v.app n y)) ≫ F =
      joinMap (𝟙 L) (yonedaEquiv.symm y) ≫ joinMap (𝟙 L) v ≫ F
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, yonedaEquiv_symm_comp]))

/-- Naturality of `cosliceDiagFromJoin` in the diagram: restricting along `u : L₀ ⟶ L`. -/
lemma cosliceDiagFromJoin_restrict {L₀ : SSet.{u}} (u : L₀ ⟶ L) (F : join L K ⟶ X)
    (hF : joinInl L K ≫ F = g) :
    cosliceDiagFromJoin F hF ≫ cosliceDiagRestrict u g =
      cosliceDiagFromJoin (joinMap u (𝟙 K) ≫ F)
        (by rw [← Category.assoc, ← joinInl_naturality, Category.assoc, hF]) :=
  NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    show joinMap u (𝟙 _) ≫ joinMap (𝟙 L) (yonedaEquiv.symm y) ≫ F =
      joinMap (𝟙 L₀) (yonedaEquiv.symm y) ≫ joinMap u (𝟙 K) ≫ F
    rw [← Category.assoc, ← Category.assoc, ← joinMap_comp, ← joinMap_comp, Category.comp_id,
      Category.id_comp, Category.comp_id, Category.id_comp]))

/-- Naturality of `cosliceDiagToJoin` in the shape. -/
lemma cosliceDiagToJoin_naturality {K' : SSet.{u}} (v : K' ⟶ K) (φ : K ⟶ cosliceDiag g) :
    cosliceDiagToJoin (v ≫ φ) = joinMap (𝟙 L) v ≫ cosliceDiagToJoin φ := by
  conv_lhs => rw [← cosliceDiagFromJoin_cosliceDiagToJoin φ, cosliceDiagFromJoin_naturality]
  rw [cosliceDiagToJoin_cosliceDiagFromJoin]

/-- Naturality of `cosliceDiagToJoin` in the diagram: restricting along `u : L₀ ⟶ L`. -/
lemma cosliceDiagToJoin_restrict {L₀ : SSet.{u}} (u : L₀ ⟶ L) (φ : K ⟶ cosliceDiag g) :
    cosliceDiagToJoin (φ ≫ cosliceDiagRestrict u g) = joinMap u (𝟙 K) ≫ cosliceDiagToJoin φ := by
  conv_lhs => rw [← cosliceDiagFromJoin_cosliceDiagToJoin φ, cosliceDiagFromJoin_restrict]
  rw [cosliceDiagToJoin_cosliceDiagFromJoin]

/-- The projection `X_{g/} ⟶ X` reads off the back block of the transposed morphism. -/
lemma comp_cosliceDiagProj (φ : K ⟶ cosliceDiag g) :
    φ ≫ cosliceDiagProj g = joinInr L K ≫ cosliceDiagToJoin φ := rfl

end SSet
