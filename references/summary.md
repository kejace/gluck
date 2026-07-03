# References

<!-- archon:references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `dahlberg.pdf` | Dahlberg, *The Converse of the Four Vertex Theorem*, Proc. AMS 133 (2005) 2131–2135. Primary spec for the mixed-sign extension (Thm 1.1, positivity ONLY at the two maxima). §1: arc-length repr (1.1)–(1.4) [D-A]. §2: Prop 2.1 (bicircle closure iff antipodal arcs), Props 2.2/2.3 (Möbius `g_β` — SKIPPED in-tree, subsumed by `errorMap`/`exists_closing_configuration`). §3: plane-case proof, Step 1 (η, `a(1−f)+bf+e`, `∫\|e\|<Cε`) [D-B] + Step 2 (closing param over the disk, `F*→F`, `\|α−α*\|≤Cε`) [D-C]. | `Read` with `pages: "1-5"` (whole 5-page paper, ~131 KB extracted; renders all formulas + the §3 proof). Page n = trailing standalone integer 213n. |
| `deturck-gluck-fourvertex.pdf` / `.txt` | DeTurck, Gluck, Pomerleano, Vick, *The Four Vertex Theorem and its Converse* (2006 survey). Contains Gluck's 1971 proof of the converse for **strictly positive** curvature in §III–IV (sections 4–9, pp. 9–16): reconstruction curve `α(θ)=∫₀^θ e^{iφ}/κ(φ)dφ`, error vector `E=∫₀^{2π} e^{iθ}/κ dθ`, winding-number argument in `Diff(S¹)`, Prop 9.1 (closure iff opposite arcs equal). Dahlberg's full converse (mixed sign) is in §IV — out of project scope. | `.txt` is a clean `pdftotext` extract; `Read` the `.txt` directly (51 KB, whole file fine). Page numbers in the text are the trailing standalone integers. Gluck's positive case = lines ~149–298. |
| `0308159v2.pdf` | Katriel, *From Rolle's Theorem to the Sturm-Hurwitz Theorem*, arXiv:math/0308159v2 (2003). Elementary-calculus proof of the **forward** Sturm-Hurwitz theorem: a 2π-periodic `f` with Fourier series starting at harmonic `n` has ≥`2n` zeros in `[0,2π)`. CONTEXT ONLY — forward direction, underlies the DIRECT four-vertex theorem (`ρ' ⊥ {1,cosα,sinα}` ⇒ ≥4 vertices), NOT the converse the project proves. Not used in-tree. | `pdftotext` clean, ~6 pp. |
| `0710.5902v1.pdf` | Tabachnikov, *Converse Sturm-Hurwitz-Kellogg theorem and related results*, arXiv:0710.5902v1 (2007). **Converse Sturm-Hurwitz-Kellogg** (Thm 1): continuous `f` on S¹ with ≥`n+1` sign changes ⇒ ∃ orientation-preserving diffeo `φ` with `f∘φ ⊥ Chebyshev system Vⁿ`. **The converse four-vertex theorem is the special case `V={1,cosα,sinα}`** (§1). Confirms "our strategy of proof is that of Gluck" = the SAME winding/degree argument used in-tree; Example 1.1 Steps 1–4 = clean template for D-B/D-C (step-function target → ε-close-in-measure diffeo → finite-dim family, `F(0)=0`, boundary winding ⇒ zero). NOT forward Sturm-Hurwitz. | `pdftotext` clean; Thm 1 + Example 1.1 on pp. 1–3. |
<!-- Example row (delete once you have real entries):                   -->
<!-- | `paper.pdf` | Source paper for chapter 3 | `Read` with `pages: "1-12"` (poppler installed); for the appendix tables, `pdftotext paper.pdf - \| sed -n '120,180p'` was clearer. |  -->

<!-- Rules of thumb when filling in `How to read`:                       -->
<!--   * If `Read` worked out of the box, write `Read` (and any options   -->
<!--     you needed, e.g. `pages: "1-5"` for long PDFs).                  -->
<!--   * If `Read` failed and you fell back to a shell command, record   -->
<!--     the exact command (e.g. `pdftotext file.pdf -`, `pandoc … -t    -->
<!--     markdown`, `unzip -p archive.zip path/inside.tex`).             -->
<!--   * If a file is binary / opaque (e.g. a Mathematica notebook with  -->
<!--     no useful plain-text export), say so — that saves the next      -->
<!--     agent from trying.                                              -->
<!--   * When in doubt, prefer the cheapest tool that gives you the part -->
<!--     you actually need (a page range, a single table) over loading   -->
<!--     the whole file.                                                 -->
