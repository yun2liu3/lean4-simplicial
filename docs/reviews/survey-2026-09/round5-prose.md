# Review round 5: prose consolidation (fresh reviewer, 2026-09-28)

1. §0/§5/§6 repeat "pin older than master"; "exact date not looked up" adds nothing. SHOULD
2. "not found" vs "not yet" vs "none yet" vs "Missing" drift; use "not found" for greps, "not yet" for reedy modules. MUST
3. "anodyne map" vs "anodyne extension": use "extension" (Mathlib's `anodyneExtensions`). MUST
4. §1 "`SimplicialHomotopy/` supplies most of these" overclaims: Joyal structure and categorical equivalences are open. MUST
5. The Kan–Quillen / Riou fact appears five times; keep §2 table and §3 list, shorten §1, delete §3 "Consequence". SHOULD
6. §3 compares a 2026 all-Mathlib count with a 2025 AlgebraicTopology count; give comparable counts. MUST
7. §3 "Direction" bullet list repeats the table; reduce to one sentence. SHOULD
8. §5 `Simplicial/` "would not build ... That was not tried" contradicts itself; cut repeats of §1/§6. MUST
9. §5 Verdict column is "superseded" everywhere; drop it; say which side lacks `δ_comp_σ_of_gt`. SHOULD
10. Overlong table cells (cofinal row, SimplexCategory row, simplicial-sets row of §3, risk row). SHOULD
11. Markdown: link reedy; give `Fun(A, X)` its Lean form once; "channel `#mathlib4`"; cut "nothing is sent from here". NIT
