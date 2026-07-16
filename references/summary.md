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
| `23.pdf` | B.E.J. Dahlberg, *A Discrete Four Vertex Theorem* (posthumous; prepared by Adolfsson & Kumlin, Chalmers ~2000). **The mixed-curvature forward DFV** — resolves the "obtain!" item of `discrete_plan.md` §6 item 5. Thm 1 (DFV, p.1): simple closed polygon + *locally regular* + vertices not on a circle ⇒ discrete curvature k has ≥2 local maxima + ≥2 local minima. Nomenclature (p.2): discrete circle of curvature ρ(P) through vertex + 2 neighbours, disk ω(P), k(P) = ±1/R(P) with sign by interior angle α(P) ≶ π, k=0 collinear (**≡ our `signedMengerR2` on ccw simple polygons**); plateau-aware local extrema via intervals I(f,P)/Î; sector 𝒜(P). Def 1 (p.3): locally regular ⇔ centre of ρ(P) ∈ 𝒜(P); Prop 1 sufficient: all α ∈ [π/2, 3π/2], or equilateral. Thm 2 = Cauchy's Lemma (Schoenberg–Zaremba); Lemma 2/Thm 3 smooth analogues; Thm 6 (CDFV, p.8) strictly convex case; §4 proof via half-plane monotonicity δ(P,e) (Lemma 8) + circumscribed-disk comparison (Lemma 10) — elementary, no degree theory, formalizable (future `Forward.lean` route). Bilinski 1963 = convex-obtuse predecessor. NOTE: the killer example (M,−ε,M,−ε) shows his conclusion class (2 max + 2 min) is strictly weaker than realizability — forward-only, consistent with N1. | `Read` with `pages: "1-10"` and `"11-16"` (16-page scanned-style PDF, renders fine; statements pp. 1–3, CDFV p. 8, main proof pp. 11–14). |
| `deturck-gluck-fourvertex.pdf` / `.txt` | DeTurck, Gluck, Pomerleano, Vick, *The Four Vertex Theorem and its Converse* (2006 survey). Contains Gluck's 1971 proof of the converse for **strictly positive** curvature in §III–IV (sections 4–9, pp. 9–16): reconstruction curve `α(θ)=∫₀^θ e^{iφ}/κ(φ)dφ`, error vector `E=∫₀^{2π} e^{iθ}/κ dθ`, winding-number argument in `Diff(S¹)`, Prop 9.1 (closure iff opposite arcs equal). Dahlberg's full converse (mixed sign) is in §IV — out of project scope. | `.txt` is a clean `pdftotext` extract; `Read` the `.txt` directly (51 KB, whole file fine). Page numbers in the text are the trailing standalone integers. Gluck's positive case = lines ~149–298. |
| `0308159v2.pdf` | Katriel, *From Rolle's Theorem to the Sturm-Hurwitz Theorem*, arXiv:math/0308159v2 (2003). Elementary-calculus proof of the **forward** Sturm-Hurwitz theorem: a 2π-periodic `f` with Fourier series starting at harmonic `n` has ≥`2n` zeros in `[0,2π)`. CONTEXT ONLY — forward direction, underlies the DIRECT four-vertex theorem (`ρ' ⊥ {1,cosα,sinα}` ⇒ ≥4 vertices), NOT the converse the project proves. Not used in-tree. | `pdftotext` clean, ~6 pp. |
| `0710.5902v1.pdf` | Tabachnikov, *Converse Sturm-Hurwitz-Kellogg theorem and related results*, arXiv:0710.5902v1 (2007). **Converse Sturm-Hurwitz-Kellogg** (Thm 1): continuous `f` on S¹ with ≥`n+1` sign changes ⇒ ∃ orientation-preserving diffeo `φ` with `f∘φ ⊥ Chebyshev system Vⁿ`. **The converse four-vertex theorem is the special case `V={1,cosα,sinα}`** (§1). Confirms "our strategy of proof is that of Gluck" = the SAME winding/degree argument used in-tree; Example 1.1 Steps 1–4 = clean template for D-B/D-C (step-function target → ε-close-in-measure diffeo → finite-dim family, `F(0)=0`, boundary winding ⇒ zero). NOT forward Sturm-Hurwitz. | `pdftotext` clean; Thm 1 + Example 1.1 on pp. 1–3. |
| `spaceform_notes.md` | **Active-phase spec for the S² extension** (project-authored derivation notes, marked active iter-042): stereographic disk model, conformal geodesic-curvature law `κ_S=(1+\|z\|²)/2·κ_E−⟨z,n⟩` (outward normal), tangent-angle gauge speed solve, S² vs H² analysis, "THE CRUX AND ITS RESOLUTION" (admissible-domain confinement), mixed-sign stage-2 discussion. Backs `Gluck_Sphere.tex`; will back `Gluck_SphereMixed.tex`. | Plain Markdown; `Read` directly (whole file fine). |
| `pak-lectures-discrete-polyhedral.pdf` | Pak, *Lectures on Discrete and Polyhedral Geometry*. §21 = discrete four-vertex survey (Thm 21.4, Cor 21.5/21.18 signed Menger convention, §21.10 "we are not aware of a nontrivial discrete version" — the novelty quote); §22 Cauchy lemma; §35 Alexandrov Mapping Lemma (reserve degree engine §5.6). Primary literature anchor for the discrete program. | Large PDF — `Read` with narrow `pages:` ranges; locate sections first via `pdftotext pak-lectures-discrete-polyhedral.pdf - \| grep -n "21\."`. |
| `verify_discrete_formulas.py` / `verify_discrete_closing.py` / `verify_dfv_necessity.py` | Numeric gates for the discrete program (numpy-only). `formulas`: (TC)/(TA) law all cycle types, SO(3)/SO(2,1) holonomy, spin −I. `closing` (§5.0 gate): R² Gauss–Newton — N0/N1/killer confirmed unrealizable; mixed + κ=0 examples close. `dfv_necessity` (iter-060 go/no-go): `κ=2+sin(2πi/n)` (positive, 2 extrema) NO closure at n∈{6,8,12,24,40}×400 starts; 4-extrema control closes simply — DFV-necessity framing stands. | `python3 <script>` from `references/`; `dfv_necessity` imports `closing`. Slow (~40 min); pipe-buffered — use `python3 -u` for live output. |
| `../discrete_plan.md` (repo root) | Discrete (Menger) converse four-vertex program spec, revised 2026-07-08 post-critique; user scope reopen 2026-07-13. §3 objects/(TA) law, §4 theorems + obstruction zoo, §5 engine + §5.0 numeric gate, §6.1 `Cap(κ)` blocker, §7 module plan + PoC gates, §8 risks. | `Read` directly (905 lines, 2 pages). |
| `gemini_transcript.txt` | iter-046 external math consult transcript (LLM-generated, gpt-5.5/gemini — NOT literature; provenance record only). Source of the truncation-decoupling + symmetric-step/half-period design ideas; every load-bearing claim was re-verified in-project before adoption (see iter-046 plan sidecar). **Do not cite as `% SOURCE`.** | Plain text; `Read` directly. |
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

## Checkout notes

- `23.pdf` is referenced by this inventory as the source for Dahlberg's
  discrete forward theorem, but it is not present in the current
  `/tmp/gluck-feat-forward/references/` checkout.  The current Lean source
  comments therefore refer to Dahlberg's discrete four-vertex paper rather than
  to a local file path.
