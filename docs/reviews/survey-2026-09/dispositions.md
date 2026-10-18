# How the review points were handled (author, 2026-09-28)

Rounds: 1 Mathlib facts, 2 Riou and `reedy` facts, 3 mathematics, 4 structure, scope and public
safety, 5 prose. Each round was a fresh reviewer. A final read-through (round 6) ran after the
rewrite.

Adopted:
- Every MUST point. The pushout-product result is now listed as proved, not as announced (1.3,
  3.1). Homotopy groups and `Ex∞` are no longer called "announced" (1.1, 2.2, 3.6, 4.3). The
  homotopy coherent nerve now carries the locally Kan hypothesis and is marked as an
  unattributed Mathlib project (1.2, 3.2). `reedy` goal 5 is no longer called written (2.1).
  The `*` globs are replaced by explicit files (2.3). The local checkout, the 2024 branch and
  the "other projects" sentence are gone (4.1, 4.2). Terminology is "anodyne extension"
  throughout (5.3, 3.8). The overclaim "supplies most of these" is fixed (5.4). Year and scope
  counts are now comparable: 2025 227/54, 2026 161/32 (2.5, 4.10, 5.6).
- Structure (4.4): summary, scope, evidence, method. `SimplicialHomotopy/` now comes before
  `Simplicial/`.
- The scope is consistent with the evidence. Isofibrations into nerves are listed as existing
  (1.6, 4.5). The Joyal structure is one project (3.4). Straightening is gated on Kan–Quillen
  (3.3). The weak equivalences are interim (4.6). The pin bump has a trigger (4.9).
  `Simplicial/` is kept frozen (4.8).
- Precision: the old `KanComplex` is Kan and nonempty (3.5); "cofinal" is tied to HTT 4.1.1.1
  and `Functor.Final` (3.7); Moss's characterization is not yet proved (3.9); "have
  counterparts" replaces "were upstreamed", and the inference is labeled (2.8, 2.9);
  project-intentions issue 5 is cited (2.8, 1.4); the fork's older Lean version is noted (2.7).
- Prose (5.1, 5.2, 5.5, 5.7–5.11): repeats merged, the Verdict column dropped, long cells
  split, links added.

Adopted differently:
- 2.6: the commit message "split files" came from the repository's local handoff note, not
  from git. It was dropped rather than cited.
- 4.8: the reviewer asked for one option for `Simplicial/`. The survey recommends keeping it
  frozen and does not change its `KanComplex`: course material is left as it was written.

Round 6 (final read-through), all 8 points adopted. Kan–Quillen now has only "some"
ingredients, without weak equivalences. `Simplicial/` is covered "up to" nonemptiness. Riou is
"the most active recent author". The scope consequences are worded as "if adopted". The
`reedy` table paths are explained, and the `PushoutObjObj` rows are glossed. Section
references are precise, and HTT is expanded at first use.

Rejected: none.
