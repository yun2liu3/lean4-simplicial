# Review round 3: mathematics (fresh reviewer, 2026-09-28)

1. The pushout-product `Λ[m+1, k] ⊗ Δ[n] ∪ Δ[m+1] ⊗ ∂Δ[n]` is a strong anodyne extension: already proved (`AnodyneExtensions/UnionProd.lean`), not "announced"; the TODO list in `AnodyneExtensions/Basic.lean` is out of date. MUST
2. "the homotopy coherent nerve is a quasicategory" needs the hypothesis: locally Kan simplicial category (Cordier–Porter, HTT 1.1.5.10). MUST
3. Straightening (HTT 2.2.1) is a Quillen equivalence and needs Kan–Quillen, which §6 puts out of scope; say so or narrow it. SHOULD
4. Joyal structure, categorical equivalences and isofibrations are one project; the library already has the isofibration lemma and the special outer horn theorem. SHOULD
5. Old `KanComplex` claim is correct; state it exactly: Kan in the old sense ⇔ Kan in Mathlib's sense and nonempty; the old `Quasicategory` is standard. SHOULD
6. Homotopy groups are not a TODO @joelriou (only `MulStruct` groundwork); "Sing X is Kan" carries his name only in `SingularSet.lean`. SHOULD
7. "cofinal" is HTT 4.1.1.1 (Kerodon: right cofinal); the 1-categorical analogue is `Functor.Final`; name Theorem A precisely (HTT 4.1.3.1). SHOULD
8. Use "anodyne extensions" throughout. NIT
9. In Mathlib, strong anodyne is defined by regular pairings; Moss's characterisation is not yet proved. NIT
10. Décalage is a model of slices, not a separate item. NIT

Checked, no issue: Kan ⇒ quasicategory; `Fun(A, X)` statements; anodyne = trivial cofibration marked TODO; `Δ[p] ⊗ Δ[q]` iso; Mathlib `KanComplex` fills `Λ[n+1, i]`; spine lemma for `Sp[n+1]`.
