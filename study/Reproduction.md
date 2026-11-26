# Reproduction report · v1.0.1

The revised articles and mathematical evidence were replayed locally on Windows x64 on 26 November 2026. The clean pre-freeze source was `244cf36e0d7fbe8c7ada048cd9a650c178e3dcc0`. The source commit of the distribution is in [REVISION.txt](REVISION.txt). The final ZIP checksum and a separate acceptance receipt accompany the distribution so that the archive can be hashed in its entirety.

## Inputs and procedure

A clean local Git clone supplied the export. Starting from its ZIP in an empty directory, `reproduce.py setup` checked the package manifest and restored 17 files from upstream commit `3389797a4aac8ed1c65e93c864cfa2305b65359a` by local Git blob lookup and SHA-256. Python was CPython 3.12.10, Git 2.54.0.windows.1, Matplotlib 3.10.8, Tectonic 0.17.0 with its cached v33 bundle, and Lean 4.28.0. Only pinned third-party Lake packages and their caches were reused. The project's own build directory initially contained zero compiled objects. The two Noto font files were checked by digest. The offline commands and source identifiers are in the [reproduction guide](README.md) and [sources](SOURCES.md).

## Observed results

| Check | Result |
|---|---|
| Numerical replay | All 11 groups completed. On the reference platform all eleven matched the archived text after normalizing newlines and terminal blank lines. |
| Mathematical output checks | 243 master-certificate lines, 21 supplementary witness lines and two lines in each of the two rounding transcripts matched automatically. The master transcript has SHA-256 `ac7495164047f392cd28b5f4bdbf416320c23b950159bfc1b42ccbcfb3ddcfb7` in UTF-8 with LF and one final newline. |
| Full-simplex and fixed-point searches | Narrow strip 6,068 boxes. Broad sub-strips 40,740 and 39,056. Width-22 independent atlas 5,638 boxes and six localized leaves, all of type 3111. Ten root brackets on five widths and 32 derivative slabs were replayed. [Certificate log](logs/certificates.txt) |
| Supplementary derivations | The 19 executable Python blocks are identical to the reviewed sources. Their proof notes are present, together with the separate rounding proof. Independent rational substitution into the [published bounds](EVIDENCE.md#error-budgets-in-the-executable-notes) gives an energy-error upper bound below $5.11\,10^{-44}$ and a coefficient-error upper bound below $6.85\,10^{-37}$. The two velocity sums are 105 and 24. |
| Comparator regression | In a scratch copy, changing the atlas total 5638 to 5637 or a printed quartic interval endpoint made the strict comparator fail. Changing only the exploratory descent-count row was accepted. The deterministic witnesses remained subject to exact comparison. |
| Lean | Twelve upstream modules rebuilt from source. The two upstream declarations and four signed-moment declarations each reported exactly `propext`, `Classical.choice` and `Quot.sound`. [Axiom transcript](logs/axioms.txt) |
| Editions | All six theorem, corollary and proposition statement environments are byte-identical to the submitted version. The 27 equation, theorem, table, figure and appendix labels retain their numbers in both editions. Both PDFs have the requested full byline on the title page and in the Author field. They contain nine distinct external citation links. |
| Typesetting and figure | English 12 pages, Traditional Chinese 10 pages. The embedded phase diagram on English page 7 and Chinese page 6 matches the pixels of its own language's regenerated PNG. Both PDFs and both PNGs reproduced byte for byte. |

The default numeric driver compares the proof-bearing transcripts. The additional eleven-way comparison above describes this reference environment. Full search trajectories may vary across systems. Theorems 5 and 6 use the analytic reductions and interval certificates identified in the [evidence index](EVIDENCE.md). The Lean declarations cover the portion specified there.

## Regenerated file digests

| Artifact | SHA-256 |
|---|---|
| [English PDF](paper-en.pdf) | `5a38da59d77d1fed8ba65ad78459dd0512e0fae5cf410fedb6ece2380013fd6d` |
| [Traditional Chinese PDF](paper-zh.pdf) | `8cca0438b6400e0e6f03007ed6497a455dd333e8074935a8e5c2a559c8376e3e` |
| [English figure](research/six-site/width-strip.png) | `0d6142f3e788c2a385ec8357bd0500ffdf1a3f345b04b39f3ced965ed7d633a7` |
| [Traditional Chinese figure](research/six-site/width-strip-zh.png) | `f8af22e9c3636eb3cadd29ef7af0e961c293c3b6e60f35524cc03e64106a58af` |

[Package-wide SHA-256 manifest](SHA256SUMS.txt) · [Response to the referee](Response-to-Reviewer.md)
