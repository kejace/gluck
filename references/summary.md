# References

<!-- archon:references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `deturck-gluck-fourvertex.pdf` / `.txt` | DeTurck, Gluck, Pomerleano, Vick, *The Four Vertex Theorem and its Converse* (2006 survey). Contains Gluck's 1971 proof of the converse for **strictly positive** curvature in §III–IV (sections 4–9, pp. 9–16): reconstruction curve `α(θ)=∫₀^θ e^{iφ}/κ(φ)dφ`, error vector `E=∫₀^{2π} e^{iθ}/κ dθ`, winding-number argument in `Diff(S¹)`, Prop 9.1 (closure iff opposite arcs equal). Dahlberg's full converse (mixed sign) is in §IV — out of project scope. | `.txt` is a clean `pdftotext` extract; `Read` the `.txt` directly (51 KB, whole file fine). Page numbers in the text are the trailing standalone integers. Gluck's positive case = lines ~149–298. |
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
