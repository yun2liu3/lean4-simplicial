/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
-- Nerves of categories
import SimplicialHomotopy.Nerve.NerveMap
import SimplicialHomotopy.Nerve.InnerFibrationToNerve
import SimplicialHomotopy.Nerve.NerveHo
import SimplicialHomotopy.Nerve.StrictFiber
import SimplicialHomotopy.Nerve.NerveGroupoidKan
import SimplicialHomotopy.Nerve.UnderNerve
import SimplicialHomotopy.Nerve.HomotopyNatTrans
-- Horns, spines and cells of products
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Horn.Spine
import SimplicialHomotopy.Horn.OuterHornLast
import SimplicialHomotopy.Horn.OuterHorn
import SimplicialHomotopy.Horn.ProductCell
-- Left, right, trivial, iso- and cocartesian fibrations; fibers
import SimplicialHomotopy.Fibration.LeftFibrations
import SimplicialHomotopy.Fibration.RightFibrations
import SimplicialHomotopy.Fibration.Isofibration
import SimplicialHomotopy.Fibration.Conservative
import SimplicialHomotopy.Fibration.Cocartesian
import SimplicialHomotopy.Fibration.Fiber
import SimplicialHomotopy.Fibration.TrivialFibration
-- Left and right anodyne extensions
import SimplicialHomotopy.Anodyne.LeftAnodyne
import SimplicialHomotopy.Anodyne.LeftAnodyneCells
import SimplicialHomotopy.Anodyne.RightAnodyne
import SimplicialHomotopy.Anodyne.RightAnodyneCells
import SimplicialHomotopy.Anodyne.CellLifting
import SimplicialHomotopy.Anodyne.UniversalColimits
import SimplicialHomotopy.Anodyne.BaseChangeClosure
import SimplicialHomotopy.Anodyne.Deformation
-- Cones and joins
import SimplicialHomotopy.Join.Cone
import SimplicialHomotopy.Join.ConeLifting
import SimplicialHomotopy.Join.Join
import SimplicialHomotopy.Join.JoinStd
import SimplicialHomotopy.Join.JoinHorn
import SimplicialHomotopy.Join.JoinAnodyne
import SimplicialHomotopy.Join.JoinExtension
-- Undercategories, slices and coslices
import SimplicialHomotopy.Slice.Undercategory
import SimplicialHomotopy.Slice.Coslice
import SimplicialHomotopy.Slice.CosliceJoin
import SimplicialHomotopy.Slice.CosliceDiagram
import SimplicialHomotopy.Slice.CosliceFibration
import SimplicialHomotopy.Slice.SliceDiagram
import SimplicialHomotopy.Slice.SliceFibration
import SimplicialHomotopy.Slice.UnderMapLeftFibration
import SimplicialHomotopy.Slice.UnderHomotopy
-- Homotopy equivalences, weak homotopy equivalences, equivalences in a quasicategory
import SimplicialHomotopy.Equivalence.WeakEquivalence
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan
import SimplicialHomotopy.Equivalence.HomotopyToConst
import SimplicialHomotopy.Equivalence.HomotopyOver
import SimplicialHomotopy.Equivalence.KanOfEquiv
import SimplicialHomotopy.Equivalence.Equivalences
import SimplicialHomotopy.Equivalence.FiberHoKan
import SimplicialHomotopy.Equivalence.PointwiseEquiv
-- Cofinal maps and Joyal's version of Quillen's Theorem A
import SimplicialHomotopy.Cofinal.Cofinal
import SimplicialHomotopy.Cofinal.CofinalBasic
import SimplicialHomotopy.Cofinal.CofinalConverse
import SimplicialHomotopy.Cofinal.Smooth
import SimplicialHomotopy.Cofinal.TheoremA
import SimplicialHomotopy.Cofinal.HTT
-- Relatively initial vertices
import SimplicialHomotopy.RelInitial.RelInitial
import SimplicialHomotopy.RelInitial.RelInitialLift
import SimplicialHomotopy.RelInitial.PrismCone
import SimplicialHomotopy.RelInitial.VerticalRetraction

/-!
# Simplicial homotopy theory and quasicategories

The root file of the library: it imports every module. The modules build on Mathlib's
`SSet`, `SimplexCategory` and `CategoryTheory.nerve`; see `docs/CONTENTS.md` for what each
folder contains.
-/
