# Contents of `SimplicialHomotopy`

The library builds on Mathlib's `SSet`, `SimplexCategory` and `CategoryTheory.nerve`. Every module
has a module docstring with its main declarations. References: [Lur09] is J. Lurie, *Higher Topos
Theory*; Kerodon is <https://kerodon.net>, cited by tag.

There is no `sorry` in the library and no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`; `scripts/AxiomReport.lean` checks this.

61 modules in 9 folders, 15254 lines, and the root file `SimplicialHomotopy.lean`, which imports
all of them.


## `Nerve/`

Nerves of categories: maps from a quasicategory to a nerve, the canonical functor to the nerve of the homotopy category, nerves of groupoids, undercategories of nerves, homotopies between nerves of functors.

| Module | Lines | Title |
|---|---:|---|
| `NerveMap` | 31 | Functoriality of `nerveMap` |
| `InnerFibrationToNerve` | 150 | Maps from a quasicategory to the nerve of a thin category are inner fibrations |
| `NerveHo` | 333 | Maps from a quasicategory to a nerve, and the canonical functor `C ⟶ N(hC)` |
| `StrictFiber` | 60 | The map `F_* = Fun(Δ[n], F)` and its strict fibers, for a map `F` to a nerve |
| `NerveGroupoidKan` | 79 | The nerve of a groupoid is a Kan complex |
| `UnderNerve` | 227 | The undercategory of a nerve is the nerve of the undercategory |
| `HomotopyNatTrans` | 328 | A simplicial homotopy between nerves is the nerve of a natural transformation |

## `Horn/`

Horns and spines: the edges of outer horns, spines are inner anodyne, Joyal's special outer horn theorem, the product cell lemma.

| Module | Lines | Title |
|---|---:|---|
| `HornEdge` | 78 | Outer horns: the initial edge, and the two horns of `Δ[1]` |
| `Spine` | 382 | The spine of a standard simplex is inner anodyne |
| `OuterHornLast` | 250 | The special outer horn theorem, last-vertex form |
| `OuterHorn` | 93 | The special outer horn theorem |
| `ProductCell` | 183 | The product cell lemma for the outer horn `Λ[n+2, 0]` |

## `Fibration/`

Left and right fibrations, isofibrations, conservativity, cocartesian edges and cocartesian fibrations, fibers over a vertex, trivial fibrations.

| Module | Lines | Title |
|---|---:|---|
| `LeftFibrations` | 112 | Left fibrations and left anodyne extensions |
| `RightFibrations` | 235 | Right fibrations and right anodyne extensions |
| `Isofibration` | 68 | Left fibrations are isofibrations |
| `Conservative` | 242 | Left and right fibrations are conservative |
| `Cocartesian` | 215 | Cocartesian edges and cocartesian fibrations of simplicial sets |
| `Fiber` | 90 | Fibers of a map of simplicial sets over a vertex |
| `TrivialFibration` | 419 | Right fibrations with weakly contractible fibers are trivial fibrations |

## `Anodyne/`

Left and right anodyne extensions: pushout-products, the small object argument for left and right horns, lifting along a filtration by cells, universal colimits and closure under base change, deformation retracts.

| Module | Lines | Title |
|---|---:|---|
| `LeftAnodyne` | 273 | Left anodyne extensions and pushout-products, left fibrations and pullbacks |
| `LeftAnodyneCells` | 123 | The small object argument for left horn inclusions |
| `RightAnodyne` | 304 | Right anodyne extensions and pushout-products, right fibrations and pullbacks |
| `RightAnodyneCells` | 144 | The small object argument for right horn inclusions |
| `CellLifting` | 311 | Cellwise lifting along the filtration of a rank function |
| `UniversalColimits` | 133 | Universal colimits in `Type` and in `SSet` |
| `BaseChangeClosure` | 252 | Closure properties of "base changes along `Q` lie in `P`" |
| `Deformation` | 107 | Deformation retracts are right anodyne |

## `Join/`

The cone `Δ[0] ⋆ K` and the join `A ⋆ B`: universal properties, joins of standard simplices, horns of a join, the pushout-join lemma.

| Module | Lines | Title |
|---|---:|---|
| `Cone` | 1530 | The cone `Δ[0] ⋆ K` |
| `ConeLifting` | 307 | Transferring lifting problems across the cone |
| `Join` | 293 | The join `A ⋆ B` of two simplicial sets |
| `JoinStd` | 383 | The join of standard simplices: `Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` |
| `JoinHorn` | 226 | Horns of a join |
| `JoinAnodyne` | 159 | The join of two subcomplexes, and the generating case of the pushout-join lemma |
| `JoinExtension` | 129 | Extending a map off the pushout-join of a boundary and an inner horn |

## `Slice/`

Undercategories, slices and coslices: the undercategory `C_{c/}` by décalage, coslices under a simplex and under a diagram, slices over a diagram, the fibrations between them.

| Module | Lines | Title |
|---|---:|---|
| `Undercategory` | 189 | The undercategory `C_{c/}` via décalage |
| `Coslice` | 301 | The coslice `X_{f/}` of a simplex, via the `p`-fold décalage |
| `CosliceJoin` | 581 | The universal property of the coslice `X_{f/}` |
| `CosliceDiagram` | 375 | The coslice of a simplicial set under a diagram |
| `CosliceFibration` | 34 | The coslice under a simplex fibres over the coslice under its boundary |
| `SliceDiagram` | 354 | The slice of a simplicial set over a diagram |
| `SliceFibration` | 173 | Kerodon 4.3.6.8 and 4.3.6.1 for an arbitrary diagram |
| `UnderMapLeftFibration` | 190 | `X_{c/} ⟶ Y_{F c/}` is a trivial fibration when `F` is a left fibration |
| `UnderHomotopy` | 338 | The fiber `E_c` as a deformation retract of `E ×_C C_{c/}` |

## `Equivalence/`

Homotopy equivalences and weak homotopy equivalences of simplicial sets, weak contractibility, equivalences in a quasicategory, pointwise detection of natural equivalences.

| Module | Lines | Title |
|---|---:|---|
| `WeakEquivalence` | 336 | Homotopy equivalences and weak homotopy equivalences of simplicial sets |
| `WeakEquivalenceKan` | 234 | Homotopy equivalences of Kan complexes: 2-of-3, anodyne maps, contractibility |
| `HomotopyToConst` | 63 | Maps out of a weakly contractible simplicial set into a Kan complex are homotopic to a constant |
| `HomotopyOver` | 66 | Homotopies over a trivial fibration |
| `KanOfEquiv` | 352 | A quasicategory in which every edge is an equivalence is a Kan complex |
| `Equivalences` | 200 | Equivalences in a quasicategory versus isomorphisms in `hC`; `toNerveHo C` is an isofibration |
| `FiberHoKan` | 433 | The fibers of `C ⟶ N(hC)` are Kan complexes |
| `PointwiseEquiv` | 314 | Natural equivalences are detected pointwise |

## `Cofinal/`

Cofinal maps, smoothness of left fibrations, and Joyal's version of Quillen's Theorem A in both directions. `HTT.lean` collects the results of the library under the names they have in the literature.

| Module | Lines | Title |
|---|---:|---|
| `Cofinal` | 75 | Cofinal maps of simplicial sets ([Lur09, 4.1.1.1]) |
| `CofinalBasic` | 381 | Basic facts about cofinal maps |
| `CofinalConverse` | 185 | Cofinal maps: the converse direction of Theorem A |
| `Smooth` | 211 | Left fibrations are smooth: base change preserves right anodyne maps |
| `TheoremA` | 144 | Joyal's Theorem A: the assembly |
| `HTT` | 170 | The former trust boundary: results from [Lur09] / Kerodon, now all proved |

## `RelInitial/`

Relatively initial vertices: lifting problems in cone form, cocartesian edges give relatively initial vertices, the prism as a cone, a vertical deformation retraction.

| Module | Lines | Title |
|---|---:|---|
| `RelInitial` | 65 | Relatively initial vertices |
| `RelInitialLift` | 581 | Cocartesian cone edges are relatively initial |
| `PrismCone` | 287 | The prism `Δ[1] ⊗ Δ[n]` is a cone |
| `VerticalRetraction` | 373 | A vertical deformation retraction onto a subcomplex of relatively initial vertices |

## Not in the library

The earlier library `Simplicial/` (see `README.md`) is separate and is not described here.
