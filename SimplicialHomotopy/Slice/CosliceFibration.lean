/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.SliceFibration

/-!
# The coslice under a simplex fibres over the coslice under its boundary

The case of **Kerodon 4.3.6.8 (Tag 01BZ)** that Kerodon Proposition 4.4.2.13 (Tag 01H0)
uses: the diagram is a simplex `f : Δ[p] ⟶ X` and it is restricted to its boundary.

* `SSet.leftFibration_cosliceDiagRestrict_boundary` : the restriction `X_{f/} ⟶ X_{f₀/}` is a
  left fibration.

This is the special case `u = ∂Δ[p].ι` of `SSet.leftFibration_cosliceDiagRestrict`, which
`Slice/SliceFibration.lean` proves for an arbitrary monomorphism `u`.
-/

universe u

open CategoryTheory Simplicial

namespace SSet

/-- **Kerodon 4.3.6.8 (Tag 01BZ)**, in the case needed for Kerodon 4.4.2.13 (Tag 01H0):
for an ∞-category `X` and a `p`-simplex `f : Δ[p] ⟶ X` with boundary `f₀ = f|∂Δ[p]`, the
restriction `X_{f/} ⟶ X_{f₀/}` is a left fibration. -/
theorem leftFibration_cosliceDiagRestrict_boundary (X : SSet.{u}) [Quasicategory X] (p : ℕ)
    (f : (Δ[p] : SSet.{u}) ⟶ X) : LeftFibration (cosliceDiagRestrict (boundary p).ι f) :=
  leftFibration_cosliceDiagRestrict X (boundary p).ι f

end SSet
