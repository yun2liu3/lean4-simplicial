# Working in this repo

The entry for every agent, whatever its engine.

<!-- hard-rules: kept by ~/github/aisystem/bin/notes_guide.py from templates/research-repo/AGENTS.md; edit it there -->
Hard rules (Claudia's cards 1a, 2a, 2b, 4a in ~/github/aisystem/rules):

- Student data (names, grades, rosters, submissions, feedback) is never opened, listed, copied or quoted.
- Write only in this repo. Never write in ~/Documents, the Obsidian vault or another person's repo.
- Nothing is committed or pushed unless Claudia asks. The one exception (a100): your own claim file `claims/<name>.md` and your own `LOG.md` bullets, each in a commit of its own (NOTES-GUIDE sections 2 and 5).
- A decision only Claudia can make goes to her with your recommendation; never guess it.

When two instructions differ, the first of these wins: Claudia's words in the session, these hard rules, the todo brief, this repo's own files below, the shared guide `NOTES-GUIDE.md`, and last the global defaults.
<!-- /hard-rules -->

Read, in this order:

1. `NOTES-GUIDE.md`: the shared rules for notes (LaTeX, shared style), the log `LOG.md` and claims (`claims/`). Copied from aisystem; never edit it here.
2. `README.md`: the two libraries, which are independent (no file of one imports the other), and how to build.
3. Lean: `lake build` runs on the Mac, and every `sorry` left in is named in `LOG.md` with its file and line; never rename an existing declaration.
4. `docs/CONTENTS.md`: the modules of `SimplicialHomotopy`; `MERGE-MANIFEST.md`: the record of the merge.
