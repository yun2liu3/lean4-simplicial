/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.Isofibration
import SimplicialHomotopy.Slice.CosliceFibration

/-!
# The special outer horn theorem, last-vertex form

**Kerodon Tag 01H0** (Proposition 4.4.2.13) in the absolute case, for the last vertex: if `X` is
an ∞-category and `σ₀ : Λ[n+2, n+2] ⟶ X` is an outer horn whose final edge `n+1 → n+2` is an
equivalence, then `σ₀` extends to `Δ[n+2]`. This is [Lur09, Proposition 1.2.5.1] / Joyal's
special outer horn theorem; `Horn/OuterHorn.lean` derives its `Λ[n+2, 0]` form
(`SSet.fillOuterHornOfIsEquiv`, re-exported as `SSet.HTT.fill_outerHorn_of_isEquiv`) from
this one by passing to the opposite simplicial set.

Kerodon's proof, in the terms of this library. Write `Δ[n+2] = Δ[n] ⋆ Δ[1]`, so that by
`SSet.stdSimplex.preimage_horn_joinIso` (Kerodon 4.3.6.16) the horn is
`(Δ[n] ⋆ Λ[1, 1]) ∪ (∂Δ[n] ⋆ Δ[1])`. A morphism out of it is a pair `(F, G)` agreeing on
`∂Δ[n] ⋆ Λ[1, 1]`. Let `f = F|Δ[n]` and `f₀ = f|∂Δ[n]`. Then

* `G` transposes to an edge `ū` of the coslice `X_{f₀/}` (`SSet.cosliceDiagFromJoin`);
* `F` transposes to a vertex `v` of `X_{f/}` lying over the target of `ū` under the
  restriction `ρ : X_{f/} ⟶ X_{f₀/}`;
* `ū` is an equivalence: its image under the projection `θ : X_{f₀/} ⟶ X` is the final edge
  of `σ₀`, an equivalence by hypothesis, and `θ` is a left fibration
  (`SSet.leftFibration_cosliceDiagProj`, Kerodon 4.3.6.1) between ∞-categories, hence
  conservative (`SimplicialHomotopy.isEquiv_of_leftFibration`, Kerodon 019K);
* `ρ` is a left fibration (`SSet.leftFibration_cosliceDiagRestrict_boundary`, Kerodon 4.3.6.8),
  hence an isofibration (`SSet.exists_edge_of_leftFibration_of_isEquiv`, Kerodon 01EW), so
  `ū` lifts to an edge `e : v' → v` of `X_{f/}`;
* `e` transposes back to the required `Δ[n] ⋆ Δ[1] ⟶ X`.

* `SSet.exists_join_extension_last` : the statement for the pair `(F, G)`.
* `SSet.exists_extension_joinSub_last` : the statement for a morphism out of the union.
* `SSet.horn.edgeLast` : the final edge `n+1 → n+2` of `Λ[n+2, n+2]`.
* `SSet.fill_lastHorn_of_isEquiv` : **Kerodon 01H0**, absolute case, last vertex.
-/

universe u

open CategoryTheory Limits Opposite Simplicial SimplexCategory

namespace SSet

variable {K L X : SSet.{u}}

/-- `cosliceDiagFromJoin` only depends on the morphism. -/
lemma cosliceDiagFromJoin_congr {g : L ⟶ X} {F F' : join L K ⟶ X} (h : F = F')
    (hF : joinInl L K ≫ F = g) (hF' : joinInl L K ≫ F' = g) :
    cosliceDiagFromJoin F hF = cosliceDiagFromJoin F' hF' := by
  subst h; rfl

/-! ### The join form -/

/-- **Kerodon 01H0**, in the form of a pair of morphisms out of `Δ[p] ⋆ Λ[1, 1]` and
`∂Δ[p] ⋆ Δ[1]` agreeing on `∂Δ[p] ⋆ Λ[1, 1]`: if the edge `G|Δ[1]` is an equivalence, the pair
extends over `Δ[p] ⋆ Δ[1]`. -/
theorem exists_join_extension_last (X : SSet.{u}) [Quasicategory X] (p : ℕ)
    (F : join (Δ[p] : SSet.{u}) (Λ[1, 1] : SSet.{u}) ⟶ X)
    (G : join ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u}) (Δ[1] : SSet.{u}) ⟶ X)
    (hFG : joinMap (boundary p).ι (𝟙 (Λ[1, 1] : SSet.{u})) ≫ F =
      joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u})) Λ[1, 1].ι ≫ G)
    (hG : (Edge.mk' (yonedaEquiv (joinInr _ (Δ[1] : SSet.{u}) ≫ G))).IsEquiv) :
    ∃ H : join (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}) ⟶ X,
      joinMap (𝟙 (Δ[p] : SSet.{u})) Λ[1, 1].ι ≫ H = F ∧
        joinMap (boundary p).ι (𝟙 (Δ[1] : SSet.{u})) ≫ H = G := by
  -- the diagram `f = F|Δ[p]` and its boundary `f₀`
  have hG₀ : joinInl _ _ ≫ G = (boundary p).ι ≫ (joinInl _ _ ≫ F) := by
    rw [← Category.assoc, joinInl_naturality (boundary p).ι (𝟙 _), Category.assoc, hFG,
      ← Category.assoc, ← joinInl_naturality (𝟙 _) Λ[1, 1].ι, Category.id_comp]
  have : LeftFibration (cosliceDiagRestrict (boundary p).ι (joinInl _ _ ≫ F)) :=
    leftFibration_cosliceDiagRestrict_boundary X p _
  have : LeftFibration (cosliceDiagProj ((boundary p).ι ≫ (joinInl _ _ ≫ F))) :=
    leftFibration_cosliceDiagProj X _
  have : Quasicategory (cosliceDiag ((boundary p).ι ≫ (joinInl _ _ ≫ F))) :=
    quasicategory_of_innerFibration (cosliceDiagProj ((boundary p).ι ≫ (joinInl _ _ ≫ F)))
  -- the edge `ū` of `X_{f₀/}` transposed from `G` is an equivalence, since `θ(ū)` is
  have hū : (Edge.mk' (yonedaEquiv (cosliceDiagFromJoin G hG₀))).IsEquiv := by
    refine SimplicialHomotopy.isEquiv_of_leftFibration
      (cosliceDiagProj ((boundary p).ι ≫ (joinInl _ _ ≫ F))) (hG.ofEq ?_)
    show yonedaEquiv (joinInr _ _ ≫ G) =
      (cosliceDiagProj _).app _ (yonedaEquiv (cosliceDiagFromJoin G hG₀))
    rw [← yonedaEquiv_comp, comp_cosliceDiagProj, cosliceDiagToJoin_cosliceDiagFromJoin]
  -- `Λ[1, 1]` is the vertex `1` of `Δ[1]`
  let εIso : Δ[0] ≅ (Λ[1, 1] : SSet.{u}) :=
    stdSimplex.faceSingletonIso (1 : Fin 2) ≪≫ Subcomplex.eqToIso horn_one_one_eq_face.symm
  have hε : εIso.hom ≫ Λ[1, 1].ι = stdSimplex.δ 0 := by
    simp [εIso, stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
  -- the vertex `v` of `X_{f/}` transposed from `F`, lying over the target of `ū`
  have hφρ : cosliceDiagFromJoin F rfl ≫ cosliceDiagRestrict (boundary p).ι (joinInl _ _ ≫ F) =
      Λ[1, 1].ι ≫ cosliceDiagFromJoin G hG₀ := by
    rw [cosliceDiagFromJoin_restrict, cosliceDiagFromJoin_naturality]
    exact cosliceDiagFromJoin_congr hFG _ _
  have hρv : (cosliceDiagRestrict (boundary p).ι (joinInl _ _ ≫ F)).app _
      (yonedaEquiv (εIso.hom ≫ cosliceDiagFromJoin F rfl)) =
      (cosliceDiag _).δ 0 (yonedaEquiv (cosliceDiagFromJoin G hG₀)) := by
    rw [← yonedaEquiv_comp, Category.assoc, hφρ, reassoc_of% hε, stdSimplex.yonedaEquiv_δ_comp]
  -- lift `ū` to an edge `e : v' → v` of `X_{f/}` (a left fibration is an isofibration)
  obtain ⟨v', e, he⟩ := exists_edge_of_leftFibration_of_isEquiv _ hū _ hρv
  -- transpose `e` back
  have hψρ : yonedaEquiv.symm e.edge ≫ cosliceDiagRestrict (boundary p).ι (joinInl _ _ ≫ F) =
      cosliceDiagFromJoin G hG₀ := by
    rw [yonedaEquiv_symm_comp, he]
    exact Equiv.symm_apply_apply _ _
  have hψv : Λ[1, 1].ι ≫ yonedaEquiv.symm e.edge = cosliceDiagFromJoin F rfl := by
    rw [← cancel_epi εIso.hom, reassoc_of% hε, stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq,
      Equiv.symm_apply_apply]
  refine ⟨cosliceDiagToJoin (yonedaEquiv.symm e.edge), ?_, ?_⟩
  · rw [← cosliceDiagToJoin_naturality, hψv, cosliceDiagToJoin_cosliceDiagFromJoin]
  · rw [← cosliceDiagToJoin_restrict, hψρ, cosliceDiagToJoin_cosliceDiagFromJoin]

/-! ### The union form -/

/-- `A₀ ⋆ B₀ ⊆ A ⋆ B₀` inside `A ⋆ B`, read through the identifications
`SSet.Subcomplex.joinSubIso` and `SSet.Subcomplex.joinSubRightIso`. -/
@[reassoc]
lemma Subcomplex.joinMap_ι_id_joinSubRightIso_hom {A B : SSet.{u}} (A₀ : A.Subcomplex)
    (B₀ : B.Subcomplex) :
    joinMap A₀.ι (𝟙 (B₀ : SSet.{u})) ≫ (Subcomplex.joinSubRightIso A B₀).hom =
      (Subcomplex.joinSubIso A₀ B₀).hom ≫
        Subcomplex.homOfLE (Subcomplex.joinSub_mono le_top le_rfl) := by
  rw [← cancel_mono (Subcomplex.joinSub (⊤ : A.Subcomplex) B₀).ι]
  simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.joinSubRightIso_hom_ι,
    Subcomplex.joinSubIso_hom, Subcomplex.joinToSub_ι, ← joinMap_comp, Category.comp_id,
    Category.id_comp]

/-- `A₀ ⋆ B₀ ⊆ A₀ ⋆ B` inside `A ⋆ B`, read through the identifications
`SSet.Subcomplex.joinSubIso` and `SSet.Subcomplex.joinSubLeftIso`. -/
@[reassoc]
lemma Subcomplex.joinMap_id_ι_joinSubLeftIso_hom {A B : SSet.{u}} (A₀ : A.Subcomplex)
    (B₀ : B.Subcomplex) :
    joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι ≫ (Subcomplex.joinSubLeftIso A₀ B).hom =
      (Subcomplex.joinSubIso A₀ B₀).hom ≫
        Subcomplex.homOfLE (Subcomplex.joinSub_mono le_rfl le_top) := by
  rw [← cancel_mono (Subcomplex.joinSub A₀ (⊤ : B.Subcomplex)).ι]
  simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.joinSubLeftIso_hom_ι,
    Subcomplex.joinSubIso_hom, Subcomplex.joinToSub_ι, ← joinMap_comp, Category.comp_id,
    Category.id_comp]

/-- **Kerodon 01H0**, for a morphism out of the union `(Δ[p] ⋆ Λ[1, 1]) ∪ (∂Δ[p] ⋆ Δ[1])`
inside `Δ[p] ⋆ Δ[1]`: if its restriction to the edge `Δ[1]` of the second piece is an
equivalence, it extends over `Δ[p] ⋆ Δ[1]`. -/
theorem exists_extension_joinSub_last (X : SSet.{u}) [Quasicategory X] (p : ℕ)
    (τ₀ : ((Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[1, 1] ⊔
      Subcomplex.joinSub (boundary p) (⊤ : (Δ[1] : SSet.{u}).Subcomplex) : _) : SSet.{u}) ⟶ X)
    (hτ : (Edge.mk' (yonedaEquiv (joinInr _ (Δ[1] : SSet.{u}) ≫
      (Subcomplex.joinSubLeftIso (boundary p) (Δ[1] : SSet.{u})).hom ≫
        Subcomplex.homOfLE le_sup_right ≫ τ₀))).IsEquiv) :
    ∃ H : join (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}) ⟶ X,
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[1, 1] ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫ H = τ₀ := by
  have hinf : Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[1, 1] ⊓
      Subcomplex.joinSub (boundary p) (⊤ : (Δ[1] : SSet.{u}).Subcomplex) =
      Subcomplex.joinSub (boundary p) Λ[1, 1] := by
    rw [Subcomplex.joinSub_inf, top_inf_eq, inf_top_eq]
  have bsq : Subcomplex.BicartSq
      (Subcomplex.joinSub (boundary p) Λ[1, 1])
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[1, 1])
      (Subcomplex.joinSub (boundary p) (⊤ : (Δ[1] : SSet.{u}).Subcomplex))
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[1, 1] ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[1] : SSet.{u}).Subcomplex)) := ⟨rfl, hinf⟩
  set F := (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[1, 1]).hom ≫
    Subcomplex.homOfLE bsq.le₂₄ ≫ τ₀ with hFdef
  set G := (Subcomplex.joinSubLeftIso (boundary p) (Δ[1] : SSet.{u})).hom ≫
    Subcomplex.homOfLE bsq.le₃₄ ≫ τ₀ with hGdef
  have hFG : joinMap (boundary p).ι (𝟙 (Λ[1, 1] : SSet.{u})) ≫ F =
      joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u})) Λ[1, 1].ι ≫ G := by
    rw [hFdef, hGdef, Subcomplex.joinMap_ι_id_joinSubRightIso_hom_assoc,
      Subcomplex.joinMap_id_ι_joinSubLeftIso_hom_assoc]
    rfl
  obtain ⟨H, hH₁, hH₂⟩ := exists_join_extension_last X p F G hFG hτ
  refine ⟨H, bsq.isPushout.hom_ext ?_ ?_⟩
  · rw [Subcomplex.homOfLE_ι_assoc,
      ← cancel_epi (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[1, 1]).hom,
      Subcomplex.joinSubRightIso_hom_ι_assoc, hH₁, hFdef]
  · rw [Subcomplex.homOfLE_ι_assoc,
      ← cancel_epi (Subcomplex.joinSubLeftIso (boundary p) (Δ[1] : SSet.{u})).hom,
      Subcomplex.joinSubLeftIso_hom_ι_assoc, hH₂, hGdef]

/-! ### The horn form -/

/-- **Kerodon 4.3.6.16** for the last vertex, in the indexing used below: under
`Δ[n] ⋆ Δ[1] ≅ Δ[n+2]` the horn `Λ[n+2, n+2]` is `(Δ[n] ⋆ Λ[1, 1]) ∪ (∂Δ[n] ⋆ Δ[1])`. -/
lemma stdSimplex.preimage_horn_last' (n : ℕ) :
    (horn (n + 2) (Fin.last (n + 2))).preimage (stdSimplex.joinIso n 1).hom =
      Subcomplex.joinSub (⊤ : (Δ[n] : SSet.{u}).Subcomplex) Λ[1, 1] ⊔
        Subcomplex.joinSub (boundary n) (⊤ : (Δ[1] : SSet.{u}).Subcomplex) :=
  stdSimplex.preimage_horn_joinIso n 0 (Fin.last 1)

namespace horn

/-- The final edge `n + 1 → n + 2` of the outer horn `Λ[n + 2, n + 2]`. -/
def edgeLast (n : ℕ) : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) (Fin.last (n + 2)) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
    (Fin.le_last _) (by
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
      exact Finset.card_le_two.trans (by omega))

/-- The final edge of `Λ[n + 2, n + 2]`, as a `1`-simplex of `Δ[n + 2]`, is the back edge of
`Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]`. -/
lemma edgeLast_val (n : ℕ) :
    (edgeLast.{u} n).1 = stdSimplex.objEquiv.symm (mkHom (stdSimplex.backOrderHom n 1)) := by
  refine stdSimplex.eq_of_asOrderHom_eq (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  fin_cases i <;> rfl

end horn

/-- **Kerodon Tag 01H0** (Proposition 4.4.2.13), absolute case, last vertex: in an ∞-category
an outer horn `Λ[n+2, n+2] ⟶ X` whose final edge `n+1 → n+2` is an equivalence extends to
`Δ[n+2]`. -/
theorem fill_lastHorn_of_isEquiv (X : SSet.{u}) [Quasicategory X] (n : ℕ)
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (hσ : (Edge.mk' (σ₀.app _ (horn.edgeLast n))).IsEquiv) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  -- transport along an arbitrary identification of the horn with the union, then specialise
  have key : ∀ (Q : (join (Δ[n] : SSet.{u}) Δ[1]).Subcomplex)
      (hQ : Q = Subcomplex.joinSub (⊤ : (Δ[n] : SSet.{u}).Subcomplex) Λ[1, 1] ⊔
        Subcomplex.joinSub (boundary n) (⊤ : (Δ[1] : SSet.{u}).Subcomplex))
      (ι' : (Q : SSet.{u}) ⟶ (Λ[n + 2, Fin.last (n + 2)] : SSet.{u})) [IsIso ι']
      (hι' : ι' ≫ Λ[n + 2, Fin.last (n + 2)].ι = Q.ι ≫ (stdSimplex.joinIso n 1).hom),
      ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
    intro Q hQ ι' _ hι'
    subst hQ
    -- the final edge of `σ₀` is the edge `Δ[1]` of the second piece
    have hedge : horn.edgeLast n = yonedaEquiv (joinInr _ (Δ[1] : SSet.{u}) ≫
        (Subcomplex.joinSubLeftIso (boundary n) (Δ[1] : SSet.{u})).hom ≫
          Subcomplex.homOfLE le_sup_right ≫ ι') := by
      have hinr : joinInr _ (Δ[1] : SSet.{u}) ≫ joinMap (boundary n).ι (𝟙 (Δ[1] : SSet.{u})) =
          joinInr (Δ[n] : SSet.{u}) Δ[1] := by
        rw [← joinInr_naturality, Category.id_comp]
      refine Subtype.ext ?_
      rw [horn.edgeLast_val]
      show _ = Λ[n + 2, Fin.last (n + 2)].ι.app _ (yonedaEquiv _)
      rw [← yonedaEquiv_comp]
      simp only [Category.assoc]
      rw [hι', Subcomplex.homOfLE_ι_assoc, Subcomplex.joinSubLeftIso_hom_ι_assoc,
        reassoc_of% hinr, stdSimplex.joinIso_hom_joinInr, yonedaEquiv_map]
    obtain ⟨H, hH⟩ := exists_extension_joinSub_last X n (ι' ≫ σ₀) (hσ.ofEq (by
      show σ₀.app _ (horn.edgeLast n) = yonedaEquiv _
      rw [hedge, ← yonedaEquiv_comp]
      congr 1))
    refine ⟨(stdSimplex.joinIso n 1).inv ≫ H, ?_⟩
    rw [← cancel_epi ι', ← Category.assoc, hι', Category.assoc, Iso.hom_inv_id_assoc, hH]
  exact key _ (stdSimplex.preimage_horn_last' n) (Subcomplex.preimageIso _ _).hom
    (Subcomplex.fromPreimage_ι _ _)

end SSet
