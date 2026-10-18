/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.RelInitial.RelInitial
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# The prism `Δ[1] ⊗ Δ[n]` is a cone

The poset `[1] × [n]` has least element `(0, 0)`, so it is `WithBot` of the poset
`SSet.prism.Pt n` of its other elements. Combined with `SSet.coneNerveIso` and
`SSet.prodStdSimplex.isoNerve` this gives
`SSet.prism.coneIso n : cone (nerve (Pt n)) ≅ Δ[1] ⊗ Δ[n]`, sending the cone point
to `(0, 0)` (`SSet.prism.conePt_coneIso_hom`).

Under this isomorphism the subcomplex `K n ⊔ V n`, where
`K n = unionProd {1} ∂Δ[n] = (Δ[1] ⊗ ∂Δ[n]) ∪ ({1} ⊗ Δ[n])` and `V n` is the vertex `(0, 0)`,
is `coneUnion (B₀ n)` for the subcomplex `B₀ n` of chains of `Pt n` whose projection to `[n]`
misses some nonzero vertex (`SSet.prism.preimage_KV`).

Main consequence, `SSet.prism.exists_lift_of_preimage`: if `HasConeLiftAt p y (B₀ n)`, then every
lifting problem against `p` whose source is a subcomplex `Z` of the prism with
`Z.preimage (coneIso n).hom = coneUnion (B₀ n)`, and which sends `(0, 0)` to `y`, has a solution.
It is used in `SimplicialHomotopy/RelInitial/VerticalRetraction.lean`.
-/

universe u
open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet
namespace prism

/-- The poset `[1] × [n]` without its least element `(0, 0)`. -/
abbrev Pt (n : ℕ) : Type u := {z : ULift.{u} (Fin 2 × Fin (n + 1)) // z.down ≠ (0, 0)}

/-- `WithBot (Pt n) ⟶ [1] × [n]`, sending `⊥` to `(0, 0)`. -/
def toProd (n : ℕ) : WithBot (Pt.{u} n) →o ULift.{u} (Fin 2 × Fin (n + 1)) where
  toFun w := WithBot.recBotCoe ⟨(0, 0)⟩ (fun z ↦ z.1) w
  monotone' := by
    intro a b h
    induction a using WithBot.recBotCoe with
    | bot =>
      show ULift.up ((0 : Fin 2), (0 : Fin (n + 1))) ≤ _
      exact ⟨Fin.zero_le _, Fin.zero_le _⟩
    | coe a =>
      induction b using WithBot.recBotCoe with
      | bot => exact absurd h (WithBot.not_coe_le_bot a)
      | coe b => exact (WithBot.coe_le_coe (a := a) (b := b)).1 h

@[simp] lemma toProd_bot (n : ℕ) : toProd.{u} n ⊥ = ⟨(0, 0)⟩ := rfl
@[simp] lemma toProd_coe (n : ℕ) (z : Pt.{u} n) : toProd.{u} n z = z.1 := rfl

open Classical in
/-- `[1] × [n] ⟶ WithBot (Pt n)`, sending `(0, 0)` to `⊥`. -/
noncomputable def ofProd (n : ℕ) : ULift.{u} (Fin 2 × Fin (n + 1)) →o WithBot (Pt.{u} n) where
  toFun z := if h : z.down = (0, 0) then ⊥ else ((⟨z, h⟩ : Pt.{u} n) : WithBot (Pt.{u} n))
  monotone' := by
    intro a b h
    by_cases ha : a.down = (0, 0)
    · simp only [ha, ↓reduceDIte, bot_le]
    · have hb : b.down ≠ (0, 0) := by
        intro hb
        apply ha
        have h' : a.down ≤ b.down := h
        rw [hb] at h'
        exact Prod.ext (nonpos_iff_eq_zero.1 h'.1) (nonpos_iff_eq_zero.1 h'.2)
      simp only [ha, hb, ↓reduceDIte]
      exact WithBot.coe_le_coe.2 h

lemma ofProd_toProd (n : ℕ) (w : WithBot (Pt.{u} n)) : ofProd n (toProd n w) = w := by
  induction w using WithBot.recBotCoe with
  | bot => simp [ofProd]
  | coe z => simp [ofProd, z.2]

lemma toProd_ofProd (n : ℕ) (z : ULift.{u} (Fin 2 × Fin (n + 1))) : toProd n (ofProd n z) = z := by
  by_cases h : z.down = (0, 0)
  · show toProd n (if h' : z.down = (0, 0) then ⊥ else _) = z
    simp only [h, ↓reduceDIte, toProd_bot]
    exact ULift.ext _ _ h.symm
  · simp [ofProd, h]

/-- `nerve (WithBot (Pt n)) ≅ nerve ([1] × [n])`. -/
noncomputable def nerveIso (n : ℕ) :
    nerve (WithBot (Pt.{u} n)) ≅ nerve (ULift.{u} (Fin 2 × Fin (n + 1))) where
  hom := nerveMap (toProd n).monotone.functor
  inv := nerveMap (ofProd n).monotone.functor
  hom_inv_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦
    nerve.ext_of_isThin (funext fun _ ↦ ofProd_toProd n _))
  inv_hom_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦
    nerve.ext_of_isThin (funext fun _ ↦ toProd_ofProd n _))

/-- The prism `Δ[1] ⊗ Δ[n]` as the cone `Δ[0] ⋆ nerve (Pt n)`. -/
noncomputable def coneIso (n : ℕ) : cone (nerve (Pt.{u} n)) ≅ Δ[1] ⊗ Δ[n] :=
  coneNerveIso _ ≪≫ nerveIso n ≪≫ (prodStdSimplex.isoNerve 1 n).symm

lemma objEquiv_coneIso_hom {n m : ℕ} (x : (cone (nerve (Pt.{u} n))) _⦋m⦌) (k : Fin (m + 1)) :
    prodStdSimplex.objEquiv ((coneIso n).hom.app _ x) k =
      (toProd n (nerveCone.toFun x k)).down := rfl

/-- The vertex `(0, 0)` of the prism. -/
def v₀₀ (n : ℕ) : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)

lemma conePt_coneIso_hom (n : ℕ) : conePt _ ≫ (coneIso.{u} n).hom = const (v₀₀ n) := by
  refine NatTrans.ext (funext fun ⟨⟨m⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
  refine prodStdSimplex.objEquiv.injective (OrderHom.ext _ _ (funext fun k ↦ ?_))
  change (toProd n (nerveCone.toFun (ConeSimplex.pt _ m) k)).down = _
  rw [nerveCone.toFun_of_lt _ k k.isLt]
  rfl

/-- The chains of `[1] × [n]` which avoid `(0, 0)`, or are constant at `(0, 0)`, or miss some
`i ≠ 0` in the second coordinate: the simplices of `(Δ[1] ⊗ ∂Δ[n]) ∪ ({1} ⊗ Δ[n]) ∪ {(0, 0)}`
(`mem_KV_iff`), and of `(Δ[0] ⋆ B₀) ∪ nerve (Pt n)` (`mem_coneUnion_iff`). -/
def ChainCond {m n : ℕ} (f : Fin (m + 1) → Fin 2 × Fin (n + 1)) : Prop :=
  (∀ k, f k ≠ (0, 0)) ∨ (∀ k, f k = (0, 0)) ∨ ∃ i, i ≠ 0 ∧ ∀ k, (f k).2 ≠ i

lemma chainCond_iff {m n : ℕ} (f : Fin (m + 1) →o Fin 2 × Fin (n + 1)) :
    ChainCond f ↔
      ((∃ j, ∀ k, (f k).2 ≠ j) ∨ ∀ k, (f k).1 = 1) ∨ ∀ k, (f k).1 = 0 ∧ (f k).2 = 0 := by
  have h2 : ∀ a : Fin 2, a ≠ 0 → a = 1 := by
    intro a ha; exact Fin.ext (by have := a.isLt; have : (a : ℕ) ≠ 0 := Fin.val_ne_iff.2 ha; omega)
  constructor
  · rintro (h | h | ⟨i, -, h⟩)
    · by_cases hs : ∃ j, ∀ k, (f k).2 ≠ j
      · exact Or.inl (Or.inl hs)
      · push Not at hs
        obtain ⟨k₀, hk₀⟩ := hs 0
        have h1 : (f k₀).1 = 1 := h2 _ (fun h' ↦ h k₀ (Prod.ext h' hk₀))
        refine Or.inl (Or.inr fun k ↦ ?_)
        rcases le_total k₀ k with hk | hk
        · have := (f.monotone hk).1
          rw [h1] at this
          exact le_antisymm (Fin.le_last _) this
        · have := (f.monotone hk).2
          rw [hk₀] at this
          have h0 : (f k).2 = 0 := le_antisymm this (Fin.zero_le _)
          exact h2 _ (fun h' ↦ h k (Prod.ext h' h0))
    · exact Or.inr fun k ↦ ⟨congrArg Prod.fst (h k), congrArg Prod.snd (h k)⟩
    · exact Or.inl (Or.inl ⟨i, h⟩)
  · rintro ((⟨j, h⟩ | h) | h)
    · by_cases hj : j = 0
      · subst hj
        exact Or.inl fun k hk ↦ h k (congrArg Prod.snd hk)
      · exact Or.inr (Or.inr ⟨j, hj, h⟩)
    · exact Or.inl fun k hk ↦ by have := h k; rw [hk] at this; simp at this
    · exact Or.inr (Or.inl fun k ↦ Prod.ext (h k).1 (h k).2)

lemma toProd_down_eq_zero_iff (n : ℕ) (w : WithBot (Pt.{u} n)) :
    (toProd n w).down = (0, 0) ↔ w = ⊥ := by
  induction w using WithBot.recBotCoe with
  | bot => exact iff_of_true rfl rfl
  | coe z => exact iff_of_false z.2 WithBot.coe_ne_bot

/-- The subcomplex `B₀` of `nerve (Pt n)`: chains missing some `i ≠ 0` in the second
coordinate. -/
def B₀ (n : ℕ) : (nerve (Pt.{u} n)).Subcomplex where
  obj U := {s | ∃ i : Fin (n + 1), i ≠ 0 ∧ ∀ k, (s.obj k).1.down.2 ≠ i}
  map f s hs := by
    obtain ⟨i, hi, h⟩ := hs
    exact ⟨i, hi, fun k ↦ h _⟩

/-- `(Δ[1] ⊗ ∂Δ[n]) ∪ ({1} ⊗ Δ[n])`. -/
abbrev K (n : ℕ) : (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (stdSimplex.face {1}) (boundary n)

/-- The vertex `{(0, 0)}`. -/
abbrev V (n : ℕ) : (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  (stdSimplex.face {0}).prod (stdSimplex.face {0})

lemma mem_KV_iff {n m : ℕ} (z : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋m⦌) :
    z ∈ (K n ⊔ V n).obj _ ↔ ChainCond (prodStdSimplex.objEquiv z) := by
  rw [chainCond_iff]
  change (z ∈ (K n).obj _ ∨ z ∈ (V n).obj _) ↔ _
  have hK := Subcomplex.mem_unionProd_iff (stdSimplex.face {1}) (boundary n) z
  have hb := mem_boundary_iff_notMem_range z.2
  have h1 := stdSimplex.mem_face_iff {1} z.1
  have h0 := stdSimplex.mem_face_iff {0} z.1
  have h0' := stdSimplex.mem_face_iff {0} z.2
  have hV : z ∈ (V n).obj (op ⦋m⦌) ↔ z.1 ∈ (stdSimplex.face {0}).obj (op ⦋m⦌) ∧
      z.2 ∈ (stdSimplex.face {0}).obj (op ⦋m⦌) := Iff.rfl
  rw [show z ∈ (K n).obj (op ⦋m⦌) ↔ _ from hK, hV, hb, h1, h0, h0']
  simp only [Set.mem_range, not_exists, Finset.mem_singleton, ← forall_and]
  exact Iff.rfl

lemma mem_coneUnion_iff {n m : ℕ} (x : cone (nerve (Pt.{u} n)) _⦋m⦌) :
    x ∈ (coneUnion (B₀ n)).obj _ ↔
      ChainCond (fun k ↦ (toProd n (nerveCone.toFun x k)).down) := by
  rw [show x ∈ (coneUnion (B₀ n)).obj _ ↔ (B₀ n).augMem x.y ∨ x.j = 0 from
    Iff.or Iff.rfl (Subcomplex.mem_range_coneι_iff x)]
  obtain ⟨j, k, hjk, y⟩ := x
  change j + k = m + 1 at hjk
  dsimp only [ChainCond]
  have hbot : ∀ t : Fin (m + 1), (t : ℕ) < j →
      (toProd n (nerveCone.toFun ⟨j, k, hjk, y⟩ t)).down = (0, 0) := fun t ht ↦ by
    rw [nerveCone.toFun_of_lt _ t ht]
    rfl
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine iff_of_true (Or.inr rfl) (Or.inl fun t ht ↦ ?_)
    rw [toProd_down_eq_zero_iff, nerveCone.toFun_eq_bot_iff] at ht
    exact Nat.not_lt_zero _ ht
  cases k with
  | zero =>
    exact iff_of_true (Or.inl trivial) (Or.inr (Or.inl fun t ↦ hbot t (by omega)))
  | succ k =>
    have hval : ∀ (t : Fin (m + 1)) (ht : j ≤ t),
        (toProd n (nerveCone.toFun ⟨j, k + 1, hjk, y⟩ t)).down =
          (y.obj ⟨t - j, by change (t : ℕ) - j < k + 1; omega⟩).1.down := fun t ht ↦ by
      rw [nerveCone.toFun_of_le _ t ht]
      rfl
    change (∃ i : Fin (n + 1), i ≠ 0 ∧ ∀ s : Fin (k + 1), (y.obj s).1.down.2 ≠ i) ∨ j = 0 ↔ _
    constructor
    · rintro (⟨i, hi, h⟩ | h0)
      · refine Or.inr (Or.inr ⟨i, hi, fun t ↦ ?_⟩)
        by_cases ht : (t : ℕ) < j
        · rw [hbot t ht]
          exact hi.symm
        · rw [hval t (by omega)]
          exact h _
      · omega
    · rintro (h | h | ⟨i, hi, h⟩)
      · exact absurd (hbot ⟨0, by omega⟩ hj) (h _)
      · have h' := h (Fin.last m)
        rw [hval _ (by simp only [Fin.val_last]; omega)] at h'
        exact absurd h' (y.obj _).2
      · refine Or.inl ⟨i, hi, fun s ↦ ?_⟩
        have h' := h ⟨s + j, by omega⟩
        rw [hval _ (by dsimp only; omega)] at h'
        convert h' using 5
        exact Fin.ext (by dsimp only; omega)

/-- Under `coneIso n`, the subcomplex `K n ⊔ V n` of the prism corresponds to
`coneUnion (B₀ n)`. -/
lemma preimage_KV (n : ℕ) : (K.{u} n ⊔ V n).preimage (coneIso n).hom = coneUnion (B₀ n) := by
  ext ⟨⟨m⟩⟩ x
  exact (mem_KV_iff _).trans (mem_coneUnion_iff x).symm

lemma v₀₀_mem_V (n : ℕ) : v₀₀.{u} n ∈ (V n).obj _ :=
  ⟨(stdSimplex.mem_face_iff _ _).2 fun _ ↦ Finset.mem_singleton_self _,
    (stdSimplex.mem_face_iff _ _).2 fun _ ↦ Finset.mem_singleton_self _⟩

variable {X Y : SSet.{u}}

/-- Lifting against a subcomplex `Z` of the prism which corresponds to `coneUnion (B₀ n)`, with
the vertex `(0, 0)` sent to `y`. -/
lemma exists_lift_of_preimage (p : X ⟶ Y) (y : X _⦋0⦌) (n : ℕ)
    (hy : HasConeLiftAt p y (B₀.{u} n)) (Z : (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex)
    (hZ : Z.preimage (coneIso n).hom = coneUnion (B₀ n)) (h₀₀ : v₀₀ n ∈ Z.obj _)
    (a : (Z : SSet.{u}) ⟶ X) (b : Δ[1] ⊗ Δ[n] ⟶ Y) (sq : a ≫ p = Z.ι ≫ b)
    (hv : a.app _ ⟨v₀₀ n, h₀₀⟩ = y) :
    ∃ l : Δ[1] ⊗ Δ[n] ⟶ X, Z.ι ≫ l = a ∧ l ≫ p = b := by
  let Φ := coneIso.{u} n
  let r : (coneUnion (B₀ n) : SSet.{u}) ⟶ Z :=
    Subcomplex.lift ((coneUnion (B₀ n)).ι ≫ Φ.hom) (by
      rintro _ _ ⟨x, rfl⟩
      have hx : x.1 ∈ (Z.preimage Φ.hom).obj _ := by rw [hZ]; exact x.2
      exact hx)
  let r' : (Z : SSet.{u}) ⟶ coneUnion (B₀ n) :=
    Subcomplex.lift (Z.ι ≫ Φ.inv) (by
      rintro _ _ ⟨z, rfl⟩
      rw [← hZ]
      change Φ.hom.app _ (Φ.inv.app _ z.1) ∈ Z.obj _
      have e : Φ.hom.app _ (Φ.inv.app _ z.1) = z.1 := by
        change (Φ.inv ≫ Φ.hom).app _ z.1 = z.1
        rw [Φ.inv_hom_id]
        rfl
      rw [e]
      exact z.2)
  have hrr' : r' ≫ r = 𝟙 _ := by
    rw [← cancel_mono Z.ι]
    change Z.ι ≫ Φ.inv ≫ Φ.hom = _
    rw [Φ.inv_hom_id, Category.comp_id, Category.id_comp]
  have hpt : conePtUnion (B₀ n) ≫ r = const (⟨v₀₀ n, h₀₀⟩ : (Z : SSet.{u}) _⦋0⦌) := by
    rw [← cancel_mono Z.ι, const_comp]
    exact conePt_coneIso_hom n
  obtain ⟨l, hl₁, hl₂⟩ := hy (r ≫ a) (Φ.hom ≫ b)
    (by rw [Category.assoc, sq]; rfl)
    (by rw [← Category.assoc, hpt, const_comp, hv])
  refine ⟨Φ.inv ≫ l, ?_, ?_⟩
  · change (r' ≫ (coneUnion (B₀ n)).ι) ≫ l = a
    rw [Category.assoc, hl₁, ← Category.assoc, hrr', Category.id_comp]
  · rw [Category.assoc, hl₂, ← Category.assoc, Φ.inv_hom_id, Category.id_comp]

end prism

end SSet
