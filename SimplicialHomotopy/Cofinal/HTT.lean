/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.LeftFibrations
import SimplicialHomotopy.Slice.Undercategory
import SimplicialHomotopy.Join.Cone
import SimplicialHomotopy.Join.ConeLifting
import SimplicialHomotopy.Equivalence.KanOfEquiv
import SimplicialHomotopy.Equivalence.FiberHoKan
import SimplicialHomotopy.Equivalence.WeakEquivalence
import SimplicialHomotopy.Cofinal.Cofinal
import SimplicialHomotopy.Horn.OuterHorn
import SimplicialHomotopy.Equivalence.PointwiseEquiv
import SimplicialHomotopy.Cofinal.TheoremA

/-!
# The former trust boundary: results from [Lur09] / Kerodon, now all proved

**This file is the trust boundary of the library, and it is empty of assumptions.** Every
declaration in it is a theorem of [Lur09] (Higher Topos Theory) or Kerodon, stated in the exact
generality of the source; each was originally left as `sorry` and has since been proved
elsewhere in the library, with the proof referenced here under the original name so that
downstream files need not move. The file also holds three immediate corollaries **derived** in
place (`leftFibration_underProj`, `kanComplex_of_isEquiv_edges`,
`isWeakHomotopyEquivalence_of_rlp_monomorphisms`). Nothing in the library contains `sorry`.

The convention, should a new assumption ever be needed, is `theorem … := by sorry` here,
**not** an `axiom` anywhere. That keeps each statement honest and makes discharging one a
local change. The cost is that `#print axioms` on a downstream theorem would report a bare
`sorryAx` and **cannot name which declaration of this file it came from**; the report that does
distinguish them is `scripts/AxiomReport.lean`, which lists direct
`sorry`s by module (and also catches a stray `axiom`). To see which of these a single file
uses, `grep -n HTT` it.

Conventions: "∞-category" means `[Quasicategory C]`; `C_{c/}` is `SSet.under C c`
(décalage model, `Undercategory.lean`); cofinality is `SSet.IsCofinal`
([Lur09, 4.1.1.1], tested against **right** fibrations = Kerodon's *right* cofinal,
Definition 7.2.1.1, tag 02N1); weak contractibility is Kerodon's
(`WeakEquivalence.lean`).

Each declaration records the source tag and the name of its proof.

Where each statement is proved:
* Joyal's Theorem A, both directions ([Lur09, 4.1.3.1]): `TheoremA.lean`
  (`isCofinal_of_weaklyContractible_pullback_underProj`,
  `weaklyContractible_pullback_underProj_of_isCofinal`), along Joyal's route: factor
  `p = i ≫ q` with `i` right anodyne and `q` a right fibration (`RightAnodyneCells.lean`), left
  fibrations are smooth ([Lur09, 4.1.2.15], `Smooth.lean`), `Z ×_C C_{c/}` retracts onto the
  fibre (`UnderHomotopy.lean`), a right fibration with weakly contractible fibres is a trivial
  fibration (`TrivialFibration.lean`), and cofinality is characterised on both sides
  (`CofinalBasic.lean`, `CofinalConverse.lean`);
* [Lur09, 2.1.2.3]: `ConeLifting.lean`; [Lur09, 2.1.2.2] is derived from it below;
* [Lur09, 2.1.2.6] and [Lur09, 2.1.2.7]: `LeftAnodyne.lean`;
* Joyal's special outer horn theorem (Kerodon 019F, [Lur09, 1.2.5.1]): `OuterHorn.lean`, via
  Kerodon 01H0 in `OuterHornLast.lean`; Kerodon 019D is derived from it below;
* pointwise detection of natural equivalences (Kerodon 01DK, [Lur09, 3.1.2.1]):
  `PointwiseEquiv.lean`, via the product cell lemma Kerodon 01DP in `ProductCell.lean`.
-/

universe u

open CategoryTheory Limits MonoidalCategory

open scoped Simplicial

namespace SSet.HTT

/-! ### Theorem A -/

/-- [Lur09, Theorem 4.1.3.1] (Joyal's version of Quillen's Theorem A), the direction
from the fibres to cofinality: if `p : S ⟶ C` is a map of simplicial sets with `C` an ∞-category
and,
for every object `c` of `C`, the simplicial set `S ×_C C_{c/}` is weakly contractible,
then `p` is cofinal. (Kerodon Theorem 7.2.3.1(2), Tag 02NY: `F` is *right* cofinal iff
`C ×_D D_{X/}` is weakly contractible for every object `X`. The under-categories `C_{c/}`
pair with **right** cofinality, i.e. with `SSet.IsCofinal`, which tests against right
fibrations; the slices `C_{/c}` pair with left cofinality, part (1) of the same theorem.)

Note the generality: `S` is an arbitrary simplicial set; only the target `C` is required
to be an ∞-category. -/
theorem isCofinal_of_weaklyContractible {S C : SSet.{u}} [Quasicategory C] (p : S ⟶ C)
    (h : ∀ c : C _⦋0⦌, WeaklyContractible (pullback p (C.underProj c))) :
    IsCofinal p :=
  isCofinal_of_weaklyContractible_pullback_underProj p h

/-- The converse direction of [Lur09, 4.1.3.1] (Kerodon 7.2.3.1(2), Tag 02NY). Proved in
`TheoremA.lean`. -/
theorem weaklyContractible_of_isCofinal {S C : SSet.{u}} [Quasicategory C] (p : S ⟶ C)
    (hp : IsCofinal p) (c : C _⦋0⦌) :
    WeaklyContractible (pullback p (C.underProj c)) :=
  weaklyContractible_pullback_underProj_of_isCofinal p hp c

/-! ### Left anodyne maps and cones (HTT §2.1.2) -/

/-- [Lur09, Lemma 2.1.2.3]: if `B₀ ↪ B` is left anodyne, then
`(Δ[0] ⋆ B₀) ∪ (∅ ⋆ B) ↪ Δ[0] ⋆ B` is inner anodyne (cone model and statement
`SSet.InnerAnodyneConeOfLeftAnodyne` of `Cone.lean`).

**No longer assumed — proved** in `Join/ConeLifting.lean` as
`SSet.innerAnodyneConeOfLeftAnodyne`, and kept here under its original name, so that it can be
cited from this file. Both classes are left lifting classes by definition, so the
lemma is a transfer of lifting problems across the cone's universal property `coneHomEquiv`, with
the generating left horn case `innerAnodyne_cone_horn` (`Cone.lean` (C4)) in between; no cell
induction and no appeal to 2.1.2.2. -/
theorem innerAnodyne_cone_of_leftAnodyne : InnerAnodyneConeOfLeftAnodyne.{u} :=
  SSet.innerAnodyneConeOfLeftAnodyne

/-- [Lur09, Proposition 2.1.2.2]: for an ∞-category `X` and an object `c`, the projection
`X_{c/} ⟶ X` is a left fibration. Derived from 2.1.2.3 and the universal property of the
cone (`Cone.lean`, `leftFibration_underProj_of_innerAnodyne_cone`). -/
theorem leftFibration_underProj (X : SSet.{u}) [Quasicategory X] (c : X _⦋0⦌) :
    LeftFibration (X.underProj c) :=
  leftFibration_underProj_of_innerAnodyne_cone innerAnodyne_cone_of_leftAnodyne X c


/-!
[Lur09, Proposition 2.1.2.6] (`({0} × B) ∪ (Δ[1] × B₀) ↪ Δ[1] × B` is left anodyne) and
[Lur09, Corollary 2.1.2.7] (pushout-products of monomorphisms with left anodyne maps are left
anodyne) are **proved** in `Anodyne/LeftAnodyne.lean`:
`SSet.leftAnodyneExtensions_unionProd_horn₁₀_ι`, `SSet.leftAnodyneExtensions_unionProd_ι`.
-/

/-! ### Weak equivalences -/

/-- A trivial Kan fibration is a weak homotopy equivalence. Elementary and **proved**:
`WeakEquivalence.lean` shows it is a homotopy equivalence
(`isHomotopyEquivalence_of_rlp_monomorphisms`). Kept here as a re-export only; nothing in the
library uses it. -/
theorem isWeakHomotopyEquivalence_of_rlp_monomorphisms {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    IsWeakHomotopyEquivalence f :=
  (isHomotopyEquivalence_of_rlp_monomorphisms hf).isWeakHomotopyEquivalence

/-! `weaklyContractible_of_isWeakHomotopyEquivalence` (2-out-of-3 for the map to the point)
is proved in `WeakEquivalence.lean` as
`SSet.weaklyContractible_of_isWeakHomotopyEquivalence`. -/

/-! ### Joyal's special outer horn theorem (Kerodon 019F, HTT 1.2.5.1) -/

/-- [Lur09, 1.2.5.1] / Kerodon Theorem 4.4.2.6 (Tag 019F, Joyal), implication (1) ⇒ (2):
in an ∞-category, an outer horn `Λ[n, 0] ⟶ C` (`n ≥ 2`) whose initial edge is an
equivalence admits a filler (statement `SSet.FillOuterHornOfIsEquiv`, `KanOfEquiv.lean`).
**Proved**: `OuterHornLast.lean` proves the last-vertex form, which is the
absolute case of Kerodon Proposition 4.4.2.13 (Tag 01H0), by Kerodon's route
(4.3.6.1 + 4.3.6.8 for the coslices, 019K conservativity, 01EW lifting of an equivalence along
a left fibration), and `OuterHorn.lean` transports it along `opFunctor`. Kept here under its
original name so that no downstream file changes. -/
theorem fill_outerHorn_of_isEquiv : FillOuterHornOfIsEquiv.{u} :=
  fillOuterHornOfIsEquiv

/-- Kerodon 019D: a quasicategory all of whose edges are equivalences is a Kan complex
(derived from `fill_outerHorn_of_isEquiv`). -/
theorem kanComplex_of_isEquiv_edges (C : SSet.{u}) [Quasicategory C]
    (h : ∀ {x y : C _⦋0⦌} (e : C.Edge x y), e.IsEquiv) : KanComplex C :=
  SSet.kanComplex_of_isEquiv_edges C h fill_outerHorn_of_isEquiv

/-! ### Pointwise detection of natural equivalences (Kerodon 01DK, HTT 3.1.2.1) -/

/-- Kerodon Theorem 4.4.4.4 (Tag 01DK) / [Lur09, Proposition 3.1.2.1]: a natural transformation
between functors `K ⟶ C` into an ∞-category is an equivalence iff all its components are
(statement `SSet.IsEquivOfPointwise`, `FiberHoKan.lean`).

**No longer assumed — proved** in `Equivalence/PointwiseEquiv.lean` as
`SSet.isEquivOfPointwise`, and kept here under its original name. -/
theorem isEquiv_of_pointwise : IsEquivOfPointwise.{u} :=
  isEquivOfPointwise

end SSet.HTT
