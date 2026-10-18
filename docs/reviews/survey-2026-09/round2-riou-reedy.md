# Review round 2: facts on Joël Riou's work and the reedy repository (fresh reviewer, 2026-09-28)

1. "goals 1 to 5 are written": goal 5 has a `sorry` (C.5.7, `Factorization.lean`); say goals 1–4 written. MUST
2. Homotopy groups and `Ex∞` are not announced by any TODO @joelriou; limit "announced" to Kan–Quillen, anodyne = trivial cofibration, Sing X Kan, Quillen equivalence. MUST
3. `*` globs in the 2026 table include files by others (`Topology/Convenient`, `ConvexSpace`, `DerivabilityStructure`, `DerivedCategory`); list files explicitly. MUST
4. The copyright grep misses files where he is a later holder or only under `Authors:` (e.g. `AnodyneExtensions/Inner/*`). SHOULD
5. Counts cover different scopes; add the 2026 count for `AlgebraicTopology/` (32). SHOULD
6. Commit message "split files" not checkable from git here; cite its source. SHOULD (source: the repo's local handoff note)
7. "builds against the fork" never checked; the fork pins Lean v4.32.0-rc1, older than this repo's pin. SHOULD
8. "were upstreamed" → "have counterparts in Mathlib"; label "next candidates" as inference; cite project-intentions issue #5 linked from `Reedy/Basic.lean`. SHOULD
9. `PushoutObjObj` already in Mathlib; the fork branch name suggests a refactor (inference). SHOULD
10. Paths are `Reedy/Reedy/...`; "further developed" is an inference. NIT
11. Date: the remote `main` was still at `5e5cfd8` on 2026-07-19. NIT
12. Table paths drop the `CategoryTheory/` prefix; add `Order/NonemptyFiniteChains`. NIT

Verified correct: 161 and 54 counts; most 2026 rows; the 2025 groundwork list; quoted TODOs; README goals; fork and branch; the live `sorry`s.
