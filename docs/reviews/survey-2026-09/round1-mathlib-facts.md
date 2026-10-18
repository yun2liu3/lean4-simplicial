# Review round 1: facts on Mathlib (fresh reviewer, 2026-09-28; about 45 claims checked)

1. Homotopy groups are not a TODO anywhere; only `MulStruct` prepares them. MUST
2. The homotopy coherent nerve of a Kan-enriched category is listed as an (unattributed) project in `SimplicialNerve.lean`; not "unannounced". MUST
3. The pushout-product TODO in `AnodyneExtensions/Basic.lean` is out of date (done in `UnionProd.lean`); inner variants done too. SHOULD
4. The Reedy TODO covers only the model structure (project-intentions #5), not Δ, and is unattributed. SHOULD
5. No `Path.spine`; the map is `SSet.spine`. SHOULD
6. The library already has isofibrations into nerves (`Equivalence/Equivalences.lean`, `Fibration/Isofibration.lean`). SHOULD
7. Attribute the Kan–Quillen TODO to `AnodyneExtensions/Basic.lean`, not the scoped instances. NIT
8. "Sing X is Kan" also appears, unattributed, in `SimplicialSet/KanComplex.lean`. NIT
9. The folder table omits `SingularHomology/`, `FundamentalGroupoid/`, `CechNerve` etc.; title it "selected". NIT
10. Add homotopy invariance of simplicial homology. NIT

Verified correct: all folder counts; `sSetTopAdj`; `KanComplex := IsFibrant`, `J` = horns `Λ[n+1, i]`; the anodyne and inner anodyne API; `ihom` instances; quasicategory API; model category API; nerve adjunction; `isoNerve`; `sd ⊣ ex`; `Simplicial/` comparisons; all "not found" items re-grepped.
