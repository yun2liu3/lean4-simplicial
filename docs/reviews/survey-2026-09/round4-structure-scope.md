# Review round 4: structure, scope, public safety (fresh reviewer, 2026-09-28)

1. §0 names a local checkout and a 2024 branch of unpublished work; delete. MUST
2. §6 "the owner's other formalization projects" points to private projects; give a concrete order instead. MUST
3. `Ex∞` and `πₙ` are called "announced by Riou", but no docstring TODO says so; correct. MUST
4. Order: summary and proposal first, evidence next, method last; `SimplicialHomotopy/` before `Simplicial/`. SHOULD
5. Isofibrations are already in the library (`Fibration/Isofibration`); do not list them as a continuation. SHOULD
6. §6 leaves open whether the library's weak equivalences stay; say they are interim, not extended, reconciled later. SHOULD
7. "It defines no notion that Mathlib already has" overclaims; say targeted greps found none. SHOULD
8. `Simplicial/` bullet offers two options; recommend one; changing its `KanComplex` alters course material. SHOULD
9. "move the pin forward regularly" is not actionable; give a trigger and the first check. SHOULD
10. §3 counts are not comparable (different year, different scope). SHOULD
11. Agent-log voice ("this session ...", "nothing is sent from here") in a public file. NIT
12. Headings: name §3 and §4 by content, not by a person's intent. NIT
