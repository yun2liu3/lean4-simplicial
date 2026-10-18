/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.OuterHornLast

/-!
# The special outer horn theorem

**Kerodon Tag 019F** (Theorem 4.4.2.6, (1) ⇒ (2)) / [Lur09, Proposition 1.2.5.1] / Joyal: in an
∞-category, an outer horn `Λ[n+2, 0] ⟶ C` whose initial edge `0 → 1` is an equivalence extends
to `Δ[n+2]`. This is the statement `SSet.FillOuterHornOfIsEquiv` of `Equivalence/KanOfEquiv.lean`;
`Cofinal/HTT.lean` re-exports the theorem as `SSet.HTT.fill_outerHorn_of_isEquiv`.

The proof is the last-vertex form `SSet.fill_lastHorn_of_isEquiv` (Kerodon 01H0, in
`Horn/OuterHornLast.lean`) applied to the opposite ∞-category `C.op`: under
`SSet.stdSimplex.opIso` the horn `Λ[n+2, 0].op` is `Λ[n+2, n+2]` (`SSet.op_horn`), and the
final edge `n+1 → n+2` of the latter is the initial edge `0 → 1` of the former
(`SSet.opObjEquiv_app_edgeLast`), whose image is an equivalence of `C.op` by
`SSet.Edge.IsEquiv.op`. The extension in `C.op` is transported back along the involution
`SSet.opFunctor`, which is an equivalence of categories (`SSet.opEquivalence`).

* `SSet.fillOuterHornOfIsEquiv : FillOuterHornOfIsEquiv` — **Kerodon 019F**.
-/

universe u

open CategoryTheory Simplicial SimplexCategory

namespace SSet

/-- Under any identification `j` of a copy of `Λ[n+2, n+2]` with the opposite of `Λ[n+2, 0]`
compatible with `SSet.stdSimplex.opIso`, the final edge `n+1 → n+2` goes to the initial edge
`0 → 1`. -/
lemma opObjEquiv_app_edgeLast (n : ℕ)
    (j : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ (Λ[n + 2, 0] : SSet.{u}).op)
    (hj : j ≫ opFunctor.map Λ[n + 2, 0].ι =
      Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplex.opIso.{u} ⦋n + 2⦌).inv) :
    opObjEquiv (j.app _ (horn.edgeLast n)) = horn.edge₀₁ n := by
  refine Subtype.ext ?_
  show (j ≫ opFunctor.map Λ[n + 2, 0].ι).app _ (horn.edgeLast n) = (horn.edge₀₁ n).1
  rw [hj]
  show stdSimplex.opObjEquiv.{u, u}.symm (horn.edgeLast.{u} n).1 = _
  rw [horn.edgeLast_val]
  show SSet.opObjEquiv (stdSimplex.opObjEquiv.{u, u}.symm
    (stdSimplex.objEquiv.symm (mkHom (stdSimplex.backOrderHom n 1)))) = (horn.edge₀₁.{u} n).1
  have h : ∀ k : Fin 2, ((stdSimplex.objEquiv.symm (mkHom (stdSimplex.backOrderHom n 1)) :
      (Δ[n + 2] : SSet.{u}) _⦋1⦌) k : ℕ) = n + 1 + k := fun _ ↦ rfl
  refine stdSimplex.ext _ _ fun i ↦ ?_
  rw [stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
  apply Fin.ext
  rw [Fin.val_rev, h, Fin.val_rev]
  fin_cases i <;> simp [horn.edge₀₁, stdSimplex.edge]

/-- **Kerodon Tag 019F** (Theorem 4.4.2.6, (1) ⇒ (2)), Joyal's special outer horn theorem:
in an ∞-category, an outer horn `Λ[n+2, 0] ⟶ C` whose initial edge `0 → 1` is an equivalence
extends to `Δ[n+2]`. Derived from the last-vertex form (Kerodon 01H0) by passing to `C.op`. -/
theorem fillOuterHornOfIsEquiv : FillOuterHornOfIsEquiv.{u} := by
  intro C _ n σ₀ hσ
  -- transport along an arbitrary identification of `Λ[n+2, 0].op` with `Λ[n+2, n+2]`
  have key : ∀ (Q : (Δ[n + 2] : SSet.{u}).Subcomplex) (hQ : Q = Λ[n + 2, Fin.last (n + 2)])
      (j : (Q : SSet.{u}) ⟶ (Λ[n + 2, 0].op : SSet.{u})) [IsIso j]
      (hj : j ≫ Λ[n + 2, 0].op.ι = Q.ι ≫ (stdSimplex.opIso.{u} ⦋n + 2⦌).inv),
      ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
    intro Q hQ j _ hj
    subst hQ
    -- the same statement with `Λ[n+2, 0].op` written as `opFunctor.obj Λ[n+2, 0]`
    have key' : ∀ (j : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ (Λ[n + 2, 0] : SSet.{u}).op)
        [IsIso j] (hj : j ≫ opFunctor.map Λ[n + 2, 0].ι =
          Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplex.opIso.{u} ⦋n + 2⦌).inv),
        ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
      intro j _ hj
      -- the transported horn `Λ[n+2, n+2] ⟶ C.op` has final edge the opposite of `σ₀`'s initial one
      have hτ : (Edge.mk' ((j ≫ opFunctor.map σ₀).app _ (horn.edgeLast n))).IsEquiv := by
        refine hσ.op.ofEq ?_
        show opObjEquiv.symm (σ₀.app _ (horn.edge₀₁ n)) =
          (opFunctor.map σ₀).app _ (j.app _ (horn.edgeLast n))
        rw [opFunctor_map, opObjEquiv_app_edgeLast n j hj]
      obtain ⟨τ, hτ'⟩ := fill_lastHorn_of_isEquiv C.op n (j ≫ opFunctor.map σ₀) hτ
      -- transport the filler back along the involution `opFunctor`
      refine ⟨opEquivalence.functor.preimage ((stdSimplex.opIso.{u} ⦋n + 2⦌).hom ≫ τ),
        opEquivalence.functor.map_injective ?_⟩
      rw [CategoryTheory.Functor.map_comp, Functor.map_preimage]
      show opFunctor.map σ₀ = opFunctor.map Λ[n + 2, 0].ι ≫ (stdSimplex.opIso.{u} ⦋n + 2⦌).hom ≫ τ
      rw [← cancel_epi j, reassoc_of% hj, Iso.inv_hom_id_assoc, ← hτ']
    exact @key' j ‹_› hj
  exact key (Λ[n + 2, 0].op.preimage (stdSimplex.opIso.{u} ⦋n + 2⦌).inv)
    (by rw [op_horn, Fin.rev_zero])
    (Subcomplex.preimageIso Λ[n + 2, 0].op (stdSimplex.opIso.{u} ⦋n + 2⦌).symm).hom
    (Subcomplex.fromPreimage_ι Λ[n + 2, 0].op (stdSimplex.opIso.{u} ⦋n + 2⦌).inv)

end SSet
