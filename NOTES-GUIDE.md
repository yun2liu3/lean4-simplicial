Shared guide, copied from ~/github/aisystem/templates/research-repo/; edit it there, not here.

# Notes guide

How notes are written and logged in this repo. Claudia is a mathematician; the notes are for her to read later without the source at hand.

Instructions in every research repo have one layout: `AGENTS.md` is the entry for every agent, whatever its engine, and names this guide and the repo's own rule files (conventions, README, status, briefs); `CLAUDE.md` holds only `@` lines that load them (`@AGENTS.md`, `@NOTES-GUIDE.md`, and a rule file it must always see). Rules live in one place; a new rule file gets a line in `AGENTS.md`.

When two instructions differ, the first of these wins: Claudia's words in the session, the hard rules at the top of `AGENTS.md`, the todo brief, this repo's own files (its `AGENTS.md`, conventions, briefs), this guide, and last the global defaults (such as `~/.claude/rules/latex.md`, whose page layout and colours `notes-style.sty` replaces for notes).

## 1. Organise by content

- **Notes Claudia reads are LaTeX (`.tex`); Markdown is only for logs and plumbing.** Notes: topic notes, meeting notes, surveys, reading notes, reports and checks written for her. Markdown: `LOG.md` and other logs, agent briefs, reviews, audit reports and hand-offs, README, CLAUDE.md, AGENTS.md, conventions and plans, and text meant for pasting (a WhatsApp message). One version of each note: no `.md` twin beside a `.tex`.
- One file per topic or section (a paper's section, a chapter, one idea). Name the file by its content, not by date: `notes/join-flow-categories.tex`, not `notes/2026-10-12-stuff.tex`.
- When the mathematics changes, revise the file in place. Never save a dated copy of a note (`note_v2`, `note_2026-10-12`). Git keeps the old version; the log says what changed.
- Exceptions that keep a date: meeting notes (`meetings/YYYY-MM-DD-notes.tex`) and talk notes (dated by the talk). They are records of an event; once written, change them only to correct an error, and log the correction.
- Never edit a source (book text, paper) except in the layers the repo reserves for Claudia's notes. PDFs are never committed.
- A claim is one of: proved (give the proof or reference), checked (say in which examples or by which second method), or conjecture. Never state a conjecture as a result.
- Cite with a pointer: paper, section and statement number (Thm 3.4), not just the title.

## 2. The log: `LOG.md` at the repo root

One format in every repo. Dated entries, newest first. A date heading `## YYYY-MM-DD`, then one bullet per change: `file or section: what changed (why)`. Add the bullet when you make the change; a second change on the same day goes under that day's heading, not a new one. Do not edit old entries, except to fix a wrong path.

**Committing (Claudia's decision a100, 2026-10-15).** You may commit and push your own `LOG.md` bullets without asking, in a commit that holds nothing else (stage only your lines: `git add -p LOG.md`). The change a bullet describes stays uncommitted until Claudia asks, like everything else in the repo. A push that would carry anyone's earlier unpushed commits waits for her.

```
# Log

Changes to the notes, newest first. Older history: WORKLOG.md, worklog/ (before 2026-10-15).

## 2026-10-15

- `notes/permutative-and-group-completion.tex`, group completion theorem: replaced the vague Ore-type hypothesis by the left Ore condition of Nikolaus, Thm 1 (the old hypothesis was not enough for the proof).
- `meetings/2026-10-08-notes.tex`, claim about Fix: marked as tentative (the speaker hedged).
```

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

  - Environments: `theorem proposition lemma corollary conjecture definition construction question` (accent heads), `example remark warning computation` (italic heads), `proof`; `intuition` for an explanation or picture added to a statement; `errornote gapnote opennote` for a longer error, filled gap or open question (the short marks are in section 4). Paragraph labels that are not statements (`Conventions.`, `Setup.`) are `\emph{...}` run-ins.
  - **Meeting notes:** `\notekind{Meeting notes}`, title by content, the date of the meeting in `\date`, the people in `\author`. The summary box is titled `[Decisions and next steps]`. Sections: what was discussed (one per topic), claims made (tentative ones marked), next steps with who does what.
  - **Literature maps, changelogs:** the same header and summary box; tables with `booktabs` (`longtable` for long ones).
- A long note puts each section in its own file, pulled in with `\input{section}` (or subfiles, if the repo already uses them).
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

Every agent that works in this repo claims it first, so that the work given to each is clear, also to sessions on another machine or in the cloud, and a lead sees at once when an agent has been on a task too long.

- **Names.** Every agent has a stable name, and the claim file carries it: a lead is `lead-<area>`, a worker `w-<todo>-<k>` (its lead counts `k`), a standing or cloud session its session name (`m2850-classprep`). A subagent has only an id, so whoever starts it gives it its name in the brief.
- **Claim:** before the first edit, create `claims/<name>.md`, commit it on its own and push it, so that the others see it. Your claim file and your `LOG.md` bullets (section 2) are the only things you commit and push without Claudia's go (a100); everything else waits for her. If the push would carry earlier unpushed commits, or the session cannot push, leave the claim committed locally and say so in your report. One file per agent: claims never collide.
- **What it says**, six lines in this form (a script reads them):

```
agent: w-t135-2 (Mac)
branch: main
task: convert the reading notes to LaTeX
writes: notes/, LOG.md
since: 2026-10-15 14:00
until: 2026-10-15 18:00
```

- **Before you claim, read `claims/`.** Do not write a path that another claim names; if you must, ask Claudia. Past `until`: update `until` with a one-line reason in the claim, or release it. A claim past `until` or a day old is flagged to the lead and to Claudia; never delete another agent's claim.
- **Release:** at hand-off, delete your claim file in a commit of its own and push it, as for the claim. A hand-off note goes in the repo's usual place, not in the claim.
- Claims are not the log: `LOG.md` records what changed, `claims/` who is working now.
