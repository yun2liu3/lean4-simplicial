/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Lean
import SimplicialHomotopy

/-!
# Report on `sorry` and axioms

Run by `scripts/build.py`, or by `lake env lean scripts/AxiomReport.lean`. It prints

1. every declaration of a `SimplicialHomotopy.*` module whose own type or body contains
   `sorryAx`, and every `axiom` declared in such a module;
2. the axioms that the declarations of the library refer to directly;
3. for each of the main statements below, the axioms it depends on (as `#print axioms` does);
4. the axioms that the declarations of the library depend on, all together and through
   everything they use.

The last line is `REPORT: clean` when there is no `sorry`, no new axiom, and nothing depends
on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. A main statement that
is not in the environment is reported, not skipped.
-/

open Lean

namespace SimplicialHomotopy.Report

/-- The main statements of the library. -/
def mainStatements : List Name :=
  [-- Joyal's version of Quillen's Theorem A, both directions
   `SSet.isCofinal_of_weaklyContractible_pullback_underProj,
   `SSet.weaklyContractible_pullback_underProj_of_isCofinal,
   `SSet.HTT.isCofinal_of_weaklyContractible,
   `SSet.HTT.weaklyContractible_of_isCofinal,
   -- left anodyne maps and cones
   `SSet.HTT.innerAnodyne_cone_of_leftAnodyne,
   `SSet.HTT.leftFibration_underProj,
   `SSet.leftAnodyneExtensions_unionProd_ι,
   -- Joyal's special outer horn theorem and its consequences
   `SSet.HTT.fill_outerHorn_of_isEquiv,
   `SSet.HTT.kanComplex_of_isEquiv_edges,
   `SSet.HTT.isEquiv_of_pointwise,
   `SSet.kanComplex_nerve_of_groupoid,
   `SimplicialHomotopy.isEquiv_of_leftFibration,
   `SimplicialHomotopy.isEquiv_of_rightFibration,
   -- weak equivalences and trivial fibrations
   `SSet.HTT.isWeakHomotopyEquivalence_of_rlp_monomorphisms,
   `SSet.weaklyContractible_of_homotopy_id_const,
   `SSet.rlp_monomorphisms_of_rightFibration_of_weaklyContractible_fibers,
   `SSet.rlp_monomorphisms_underMap_of_leftFibration,
   -- nerves
   `SSet.innerFibration_to_nerve,
   `SSet.innerFibration_toNerveHo,
   `SSet.quasicategory_strictFiber,
   `SimplicialHomotopy.isofibration_toNerveHo,
   `SimplicialHomotopy.kanComplex_fiberHo_of,
   `SSet.underNerveIso,
   `SSet.natTransOfHomotopy,
   -- relatively initial vertices
   `SSet.exists_verticalRetraction]

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The constants of the imported modules of the library, with their module. -/
def libraryConstants (env : Environment) : Array (Name × ConstantInfo) := Id.run do
  let mut out : Array (Name × ConstantInfo) := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`SimplicialHomotopy).isPrefixOf m then
      for ci in env.header.moduleData[i]!.constants do
        out := out.push (m, ci)
  return out

def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])

def isAxiom (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.axiomInfo _) => true
  | _ => false

/-- The axioms that the given constants depend on, through everything they use: one traversal
of the constants reachable from them. -/
def allAxioms (env : Environment) (cs : Array (Name × ConstantInfo)) : NameSet × Nat := Id.run do
  let table : Std.HashMap Name ConstantInfo := cs.foldl (fun t p ↦ t.insert p.2.name p.2) {}
  let mut visited : NameSet := {}
  let mut stack : Array Name := cs.map (·.2.name)
  let mut out : NameSet := {}
  let mut count := 0
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    count := count + 1
    match (table.get? n).orElse (fun _ ↦ env.find? n) with
    | none => continue
    | some (.axiomInfo _) => out := out.insert n
    | some ci =>
      for u in usedConstants ci do
        if !visited.contains u then stack := stack.push u
  return (out, count)

def report : CoreM Unit := do
  let env ← getEnv
  let cs := libraryConstants env
  let mods := env.header.moduleNames.filter (`SimplicialHomotopy).isPrefixOf
  let mut clean := true
  IO.println s!"{mods.size} modules, {cs.size} constants (with the auxiliary ones)"
  -- 1. direct `sorry` and declared axioms
  let mut nSorry := 0
  let mut nAxiom := 0
  for (m, ci) in cs do
    if (usedConstants ci).contains ``sorryAx then
      nSorry := nSorry + 1
      IO.println s!"  sorry in {ci.name} ({m})"
    if let .axiomInfo _ := ci then
      nAxiom := nAxiom + 1
      IO.println s!"  axiom {ci.name} ({m})"
  IO.println s!"declarations with a direct sorry: {nSorry}"
  IO.println s!"axioms declared in the library: {nAxiom}"
  if nSorry != 0 || nAxiom != 0 then clean := false
  -- 2. axioms referred to directly
  let mut direct : NameSet := {}
  for (_, ci) in cs do
    for n in usedConstants ci do
      if isAxiom env n then direct := direct.insert n
  IO.println s!"axioms referred to directly by the library: {direct.toList}"
  if direct.toList.any (!stdAxioms.contains ·) then clean := false
  -- 3. axioms of the main statements
  let mut all : NameSet := {}
  let mut missing := 0
  for n in mainStatements do
    if (env.find? n).isNone then
      missing := missing + 1
      IO.println s!"  !! NOT IN ENVIRONMENT: {n}"
    else
      let ax ← collectAxioms n
      all := ax.foldl (·.insert ·) all
      if ax.any (!stdAxioms.contains ·) then
        IO.println s!"  {n} depends on {ax.toList}"
  IO.println s!"axioms of the {mainStatements.length} main statements: {all.toList}"
  if missing != 0 || all.toList.any (!stdAxioms.contains ·) then clean := false
  -- 4. axioms of everything
  let (every, count) := allAxioms env cs
  IO.println s!"axioms of all declarations ({count} constants visited): {every.toList}"
  if every.toList.any (!stdAxioms.contains ·) then clean := false
  IO.println (if clean then "REPORT: clean" else "REPORT: NOT clean")

#eval report

end SimplicialHomotopy.Report
