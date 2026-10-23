Shared guide, copied from ~/github/aisystem/templates/research-repo/; edit it there, not here.

# Notes guide

How notes are written and logged in this repo. Claudia is a mathematician; the notes are for her to read later without the source at hand.

Instructions in every research repo have one layout: `AGENTS.md` is the entry for every agent, whatever its engine, and names this guide and the repo's own rule files (conventions, README, status, briefs); `CLAUDE.md` holds only `@` lines that load them (`@AGENTS.md`, `@NOTES-GUIDE.md`, and a rule file it must always see). Rules live in one place; a new rule file gets a line in `AGENTS.md`.

When two instructions differ, the first of these wins: your allocator's prompt (it comes from Claudia's words), the hard rules at the top of `AGENTS.md`, the todo brief, this repo's own files (its `AGENTS.md`, conventions, briefs), this guide, and last the global defaults (such as `~/.claude/rules/latex.md`, whose page layout and colours `notes-style.sty` replaces for notes).

## 1. Organise by content

- **Notes Claudia reads are LaTeX (`.tex`); Markdown is only for logs and plumbing.** Notes: topic notes, meeting notes, surveys, reading notes, reports and checks written for her. Markdown: `LOG.md` and other logs, agent briefs, reviews, audit reports and hand-offs, README, CLAUDE.md, AGENTS.md, conventions and plans, and text meant for pasting (a WhatsApp message). One version of each note: no `.md` twin beside a `.tex`.
- One file per topic or section (a paper's section, a chapter, one idea). Name the file by its content, not by date: `notes/join-flow-categories.tex`, not `notes/2026-10-12-stuff.tex`.
- When the mathematics changes, revise the file in place. Never save a dated copy of a note (`note_v2`, `note_2026-10-12`). Git keeps the old version; the log says what changed.
- Exceptions that keep a date: meeting notes (`meetings/YYYY-MM-DD-notes.tex`) and talk notes (dated by the talk). They are records of an event; once written, change them only to correct an error, and log the correction.
- Never edit a source (book text, paper) except in the layers the repo reserves for Claudia's notes. PDFs are never committed.
- A claim is one of: proved (give the proof or reference), checked (say in which examples or by which second method), or conjecture. Never state a conjecture as a result.
- Cite with a pointer: paper, section and statement number (Thm 3.4), not just the title.

## 2. The log: `LOG.md` at the repo root

One format in every repo. Dated entries, newest first. A date heading `## YYYY-MM-DD`, then one bullet per change: `file or section: what changed (why)`. A second change on the same day goes under that day's heading, not a new one. Do not edit old entries, except to fix a wrong path.

**Who writes it and commits (rule 3o; overrides a100's LOG.md bullets).** Workers never write `LOG.md`; they put detail in their hand-back. The lead checks the TLDR, and at the builder's PASS `dispatch.py` writes it as one bullet in the format below, with the todo id at the end as a record key. The repo's orchestrator commits it with the change, once the reviewers pass and its lead, if any, agrees, and pushes after Claudia accepts. Nobody else commits.

```
# Log

Changes to the notes, newest first. Older history: WORKLOG.md, worklog/ (before 2026-10-15).

## 2026-10-15

- `notes/permutative-and-group-completion.tex`, group completion theorem: replaced the vague Ore-type hypothesis by the left Ore condition of Nikolaus, Thm 1 (the old hypothesis was not enough for the proof).
- `meetings/2026-10-08-notes.tex`, claim about Fix: marked as tentative (the speaker hedged) · tNNN
```

- In a research repo that already has `LOG.md`, PASS writes one bullet there and creates no `WORKLOG.md`. Other repos keep the `WORKLOG.md` record. The bullet ends with `· tNNN` so the script can keep one record for that todo: revise/reject removes it, undo restores it, and a later PASS writes the single current bullet. Review notes stay in the todo discussion.
- The first entry of a new `LOG.md` points to the older logs of the repo (CHANGES.md, WORKLOG.md, `worklog/`, `logs/`, `log/`, STATUS.md history). They stay where they are as history; nothing is moved or rewritten.
- `.gitattributes` holds `LOG.md merge=union`, so two branches that each add bullets merge without a conflict. After such a merge, check that the bullets of one day sit under one heading.
- Name each change by its content ("replaced the Ore hypothesis"), never by a task or round number.
- Per-worker audit reports and quick captures are not the log; they may stay in `logs/` or `log/`, and `LOG.md` records only the changes made to the notes.

## 3. LaTeX essentials

- **Every note uses the shared style `notes-style.sty`** at the repo root (copied from aisystem like this guide; never edit it here). It gives every note the same look, the one of the categorification note for Ben: Palatino, a narrow text block with indented paragraphs, small-caps headings and theorem heads in one accent colour, a bar beside theorems, a washed summary box. It also defines the theorem environments, `\N \Z \Q \R \C` and the marks of section 4. Macros of this repo come after the `\usepackage` line; do not reload a package the style loads. A figure is `standalone`. Papers, and book annotations that live in the book's own source, keep their own preamble.
- **Every note follows one template.** The structure is part of the look: the style cannot make bold run-in labels look like theorems.

```latex
\documentclass[11pt,a4paper]{article}
\makeatletter\def\input@path{{./}{../}{../../}{../../../}}\makeatother
\usepackage{notes-style}
% Intuition layer (openings, bridges, intuition boxes): ON. For the precise version, statements
% and proofs only, uncomment the next line, or build with: pdflatex '\def\notesprecisebuild{}\input{main}'
% \notesprecise
% this note's macros
\title{Content title}\author{Yun Liu}\date{15 October 2026}
\notekind{Working note}          % or: Meeting notes, Reading notes, Literature map, Changelog, Talk notes
\runninghead{Short title}        % when the title is long
\begin{document}
\maketitle
\begin{summarybox}               % always first: what the note establishes, in 3-6 lines or bullets
  ... the main results, each with a \cref to where it is proved.
\end{summarybox}
\NoteStatus{proved | checked in ... | conjecture | survey}   % when the note states results
\section{...}                    % numbered sections; \section* only for References
\begin{definition}...\end{definition}   % statements are environments, never \textbf{Definition.}
\begin{theorem}[Author, Year, Thm 3.4]...\end{theorem}
\begin{proof}...\end{proof}      % or \begin{proof}[Proof sketch]
\end{document}
```

  - Environments: `theorem proposition lemma corollary conjecture definition construction question` (accent heads), `example remark warning computation` (italic heads), `proof`; `intuition`, `opening`, `bridge` for the intuition layer (below); `errornote gapnote opennote` for a longer error, filled gap or open question (the short marks are in section 4). Paragraph labels that are not statements (`Conventions.`, `Setup.`) are `\emph{...}` run-ins.
  - **Meeting notes:** `\notekind{Meeting notes}`, title by content, the date of the meeting in `\date`, the people in `\author`. The summary box is titled `[Decisions and next steps]`. Sections: what was discussed (one per topic), claims made (tentative ones marked), next steps with who does what.
  - **Literature maps, changelogs:** the same header and summary box; tables with `booktabs` (`longtable` for long ones).
- **Two layers, one source** (2026-10-23). Statements, definitions and proofs are the precise core: they stay exact and brief whoever reads them. Intuition is a separate layer, in three places only: `opening` at the start of a chapter or note (the picture before the details), `bridge` between sections or connecting results (where we are, why the next step), and `intuition` beside a statement. `\notesprecise` in the preamble, or building with `pdflatex '\def\notesprecisebuild{}\input{main}'`, drops the layer. So the core must read cleanly without it: no definition, hypothesis or step lives only in a layer box, and nothing in the core refers (`\cref`, "as explained above") into one. How much layer a note carries follows the reader's familiarity, set per note or chapter in its contract: a new topic gets openings and bridges, a familiar one may need none.
- A long note puts each section in its own file, pulled in with `\input{section}` (or subfiles, if the repo already uses them).
- **Citing another chapter is always a macro, never bare text** (2026-10-23), so that `bin/chapter_deps.py` can read the dependencies between chapters and jobs run in their order. In a book numbered globally (Vakil: 12.1.4) use `\bkref{12.1.4}`; in a book numbered chapter by chapter (Anderson–Fulton, Silverman) use `\bkxref{N}{4.1}`, defined once in the repo's macros as `\newcommand{\bkxref}[2]{\hyperref[bk:#1.#2]{Ch.\,#1, #2}}`. When you touch a passage with a bare book number or "Chapter N" pointing elsewhere, convert it.
- Words in math go in `\text{if } x>0`, never `\mathrm{if}`.
- Fractions: `\dfrac` in a display, `\tfrac` inline, never bare `\frac` inline.
- Definitions: `f \coloneqq g` (mathtools), not `=`.
- Displays: `\[...\]`, `equation*` or `align*`; never `eqnarray` or `$$`. No blank line inside an `align`. Text between lines: `\intertext{}`. Use `cases` for piecewise functions. Break a long equation before the operator (`=`, `+`), with the operator starting the new line.
- Spacing: `\int_0^1 f(x)\, dx`; align items with `\quad` or `\qquad`, never `~` or `\ `. Use `\bigl(` and `\bigr)` when `\left`/`\right` space badly.
- `\boxed` only for a key result or final answer.
- Tables: `booktabs` (`\toprule`, `\midrule`, `\bottomrule`), never `\hline` (the style loads booktabs and tabularx); `siunitx` `S` columns for decimals; `tabularx` for flexible widths.
- Macros: `\newcommand`, never `\def`; never `\over` or `\centerline`. A value used often is a macro (`\R` for `\mathbb{R}`), defined once.
- TikZ: load the needed libraries (`arrows.meta, calc, decorations.markings, patterns`); use the colours the style defines (`primary`, `secondary`, `accent`, `lightgray`); `Stealth` arrows, `thick` curves, `thin` grids; axis labels are `\node`s at the axis end. Export a standalone figure as PDF and PNG (`pdftoppm -png -r 300`).
- Emphasis in math is `\textcolor`, not bold. Build files and PDFs are not committed; a review PDF sits beside its source.

## 4. Marking and wording

- **Source error vs gap.** An error is something in the source that is false or misstated: write what is wrong, the corrected statement, and why. A gap is a step the source skips or only sketches: fill it in full, mark it as filled, and say where the source stops. Mark both visibly and in the same way each time: `\NoteError` / `\NoteGap` in TeX (book annotations keep their repo's macros, such as `\bookerr`, `\bookgap`), `**[Error]**` / `**[Gap]**` in Markdown. Mention each in the log.
- **Open questions.** `\NoteOpen` in the text, with the question stated in one sentence and what is known. Also list it under "Open" in the repo's status file, if there is one. A question that needs Claudia's decision is marked `\NoteClaudia` and carries a recommendation.
- **Uncertainty.** If a source or speaker hedged, say so ("tentative: the speaker was unsure", `\NoteTentative`); never upgrade a hedge to a claim. If only an abstract was read, say so.
- **Wording.** Plain and precise. State the hypotheses of a theorem where it is used. Name each item by its content ("the Ore condition", "Prop. C.4(iii)"), not by number alone. No filler, no slogans.

## 5. Claims: who works here now

Every agent that works in this repo claims it first, so that the work given to each is clear, also to sessions on another machine or in the cloud, and its allocator sees at once when an agent has been on a task too long. Claim only the work your allocator gave you in your prompt.

- **Names.** A name is exactly one of `orch-<repo>`, `lead-<area>`, `w-<tNNN>-<k>`, `r-<tNNN>-<k>` (the allocator counts `k` per todo), unique, and given by your allocator in your prompt; for example `w-t135-2`. An agent never names itself: one with no name asks its allocator.
- **Claim:** before the first edit, create `claims/<name>.md`, commit it on its own and push it, so that the others see it. It counts only once pushed: if the push is rejected, fetch, read `claims/` again and retry. Your claim file, and its deletion at hand-off, are the only things you commit and push yourself; everything else is committed by the orchestrator (section 2). If the session cannot push, say so to your allocator. One file per agent: claims never collide.
- **What it says**, seven lines in this form (a script reads them):

```
agent: w-t135-2 (MacBook)
allocator: lead-notes
branch: macbook/reading-notes
task: convert the reading notes to LaTeX
writes: notes/
since: 2026-10-15 14:00
until: 2026-10-15 18:00
```

- **Before you claim, read `claims/`.** If you need a path another claim names, stop and tell your allocator, who decides. Past `until`: update `until` with a one-line reason in the claim, or release it. A claim past `until` or a day old is flagged to its allocator only; never delete another agent's claim. A claim untouched for 7 days lapses and is listed for Claudia; nobody takes it over on their own.
- **Release:** at hand-off, delete your claim file in a commit of its own and push it, as for the claim. A hand-off note goes in the repo's usual place, not in the claim.
- **Two machines (rule 2e).** On the MacBook, notes work goes often to the working branch `macbook/<topic>`; for now the agent that allocated the work (its orchestrator or lead) pushes it, and who does this is open for Claudia. "Push after accept" concerns `main`: it changes only when Claudia accepts, merged by the hub's orchestrator on the Mac Mini. Commits from both machines use `49599185+yun2liu3@users.noreply.github.com` and a `Machine:` trailer.
- Claims are not the log: `LOG.md` records what changed, `claims/` who is working now.
