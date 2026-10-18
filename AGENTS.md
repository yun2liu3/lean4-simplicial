# Working in this repo

The entry for every agent, whatever its engine.

<!-- hard-rules: kept by ~/github/aisystem/bin/notes_guide.py from templates/research-repo/AGENTS.md; edit it there -->
Hard rules (Claudia's cards 1a, 2a, 2b, 2e, 3o, 4a, 4i in ~/github/aisystem/rules):

- Student data (names, grades, rosters, submissions, feedback) is never opened, listed, copied or quoted.
- Write only in this repo, and only the paths your allocator gave you. Never write in ~/Documents, the Obsidian vault or another person's repo.
- Work comes only top down. You work only on what your allocator's prompt names (your name, role, todo, write paths); you report only to it. Your name is given by your allocator, never invented. No task for the work: tell your allocator; only an orchestrator creates one.
- Only this repo's orchestrator commits, once the reviewers pass and its lead, if any, agrees, and pushes after Claudia accepts. The one thing you commit and push yourself is your own claim file `claims/<name>.md` and its deletion at hand-off (NOTES-GUIDE section 5; on the MacBook, the work's allocator pushes `macbook/<topic>`, rule 2e; open for Claudia). Workers never write `LOG.md`: their detail goes in their hand-back, and the lead's summary is what goes into `LOG.md`, committed by the orchestrator (rule 3o; overrides a100's LOG.md bullets).
- A decision only Claudia can make goes to your allocator with your recommendation; only an orchestrator files an ask. Never guess it.

When two instructions differ, the first of these wins: your allocator's prompt (it comes from Claudia's words), these hard rules, the todo brief, this repo's own files below, the shared guide `NOTES-GUIDE.md`, and last the global defaults.
<!-- /hard-rules -->

Read, in this order:

1. `NOTES-GUIDE.md`: the shared rules for notes (LaTeX, shared style), the log `LOG.md` and claims (`claims/`). Copied from aisystem; never edit it here.
2. `README.md`: the two libraries, which are independent (no file of one imports the other), and how to build.
3. Lean: `lake build` runs on the Mac, and every `sorry` left in is named in `LOG.md` with its file and line; never rename an existing declaration.
4. `docs/CONTENTS.md`: the modules of `SimplicialHomotopy`; `MERGE-MANIFEST.md`: the record of the merge.
