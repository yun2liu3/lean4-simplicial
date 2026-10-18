# lean4-simplicial

Simplicial foundations in Lean 4. The repository holds two libraries. They are independent:
no file of one imports a file of the other.

| Library | What it is | Built on |
|---|---|---|
| `SimplicialHomotopy/` | simplicial homotopy theory and quasicategories: fibrations, anodyne maps, joins and slices, weak equivalences, cofinal maps, Joyal's version of Quillen's Theorem A | Mathlib's `SSet`, Lean `v4.34.0-rc2` |
| `Simplicial/` | the earlier course project: the simplex category, simplicial objects, simplicial sets, horns, boundaries and Kan complexes, rebuilt from scratch | Mathlib's category theory only, Lean `v4.9.0-rc3` |

## SimplicialHomotopy

61 modules and a root file, about 15 000 lines, no `sorry` and no axiom beyond the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). It was developed for a formalization project
of the author and contains the part of it that is general theory. The statements follow
J. Lurie, *Higher Topos Theory* (cited as [Lur09] or HTT) and [Kerodon](https://kerodon.net)
(cited by tag).

Main results, all with full proofs:

* Joyal's version of Quillen's Theorem A, in both directions ([Lur09, 4.1.3.1]): a map
  `p : S ⟶ C` to a quasicategory is cofinal if and only if `S ×_C C_{c/}` is weakly
  contractible for every vertex `c`
  (`SSet.isCofinal_of_weaklyContractible_pullback_underProj`,
  `SSet.weaklyContractible_pullback_underProj_of_isCofinal`);
* Joyal's special outer horn theorem (Kerodon 019F), and its corollary that a quasicategory
  in which every edge is an equivalence is a Kan complex (Kerodon 019D);
* natural equivalences are detected pointwise (Kerodon 01DK);
* left and right fibrations are conservative (Kerodon 019K), and left fibrations are smooth
  ([Lur09, 4.1.2.15]);
* a right fibration with weakly contractible fibers is a trivial fibration;
* the join of simplicial sets, slices and coslices with their universal property, and the
  undercategory `C_{c/}` by décalage;
* a map from a quasicategory to the nerve of a category is an inner fibration; the nerve of a
  groupoid is a Kan complex; the undercategory of a nerve is the nerve of the undercategory.

`docs/CONTENTS.md` lists every module, by folder. `SimplicialHomotopy/Cofinal/HTT.lean`
collects the results under the names they have in the literature.

### Build

The toolchain is the one in `lean-toolchain`; Mathlib is pinned in `lakefile.toml` and
`lake-manifest.json`.

```
lake exe cache get
lake build
```

On a machine where `lake` does not start, there is a fallback that calls `lean` directly:

```
MATHLIB_BUILD=/path/to/packages python3 scripts/build.py
```

where `/path/to/packages` is a folder holding a compiled Mathlib at the pinned revision with
its dependencies (the `.lake/packages` folder of any project built against that revision).
The script compiles the modules in import order and then prints a report on `sorry` and
axioms (`scripts/AxiomReport.lean`). See the top of `scripts/build.py` for the options.

The library was last checked with `scripts/build.py`, not with `lake build`.

## Simplicial

A pedagogical reconstruction, written for a course: `SimplexCategory` with its generators
and the simplicial identities, `SimplicialObject`, `SSet`, the horns `Λ[n, i]`, the boundaries
`∂Δ[n]`, and the classes `KanComplex` and `Quasicategory`. It defines these names itself, at
the root namespace, so it cannot be imported together with Mathlib's `SSet`; this is why
`SimplicialHomotopy` is a separate library.

It was written for Lean `v4.9.0-rc3` and has not been ported to the current toolchain, so it
is not a target of `lakefile.toml`. Its original build files are in `legacy/`; to build it as
before, put the three files of `legacy/` back at the top of a checkout.
