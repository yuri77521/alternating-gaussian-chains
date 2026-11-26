# Rights, attribution and dependencies

This repository distributes the project's bilingual manuscript, research derivations, figures, proof programs and reproduction records. No repository-wide reuse license has been selected for the project's own material. The research credits in the papers and the third-party permissions below serve different purposes. A license for a build dependency applies to that dependency.

## The historical chain project

The source tree at `3389797a4aac8ed1c65e93c864cfa2305b65359a` was inspected for a license or copying notice, including the 17 file inputs. No repository-wide grant or file-level reuse license was found for those inputs at the pinned snapshot. Public access alone does not establish permission for independent redistribution. The GitHub view/fork terms are described separately in [GitHub's licensing guidance](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository).

The public Git tree and frozen release ZIP omit those 17 files. The recipient's reproduction process retrieves two Python modules, twelve upstream Lean modules, and three Lean build files directly from the public source, verifying each against the [17-file manifest](study/upstream-files.sha256). The project's own [Lean source](study/research/exact-clusters/AlternatingMoments.lean) is included in full. The public package retains the complete research derivations and all 19 executable appendix blocks. The upstream four-site formalization has its own authorship. [Pinned upstream tree](https://github.com/xiujiang4/alternating-particle-chains/tree/3389797a4aac8ed1c65e93c864cfa2305b65359a) · [fixed academic sources and contributions](study/SOURCES.md)

The authors of the original papers, repository submitters and authors credited in the earlier manuscripts are identified in the source index. PR 1 provided the balanced trial, small-floor asymptotics and the earlier collision competitor. Issue 5 provided a finite-floor four-site result. PR 7 provided a four-site displacement comparison; the six-site classifications in this study use analytic and interval proofs. The pre-freeze and manuscript commit identifiers in the historical records are provenance, not dependencies.

## Fonts in the distributed articles

| Embedded family or use | Upstream terms and accompanying text |
|---|---|
| Noto Serif CJK TC Regular and Bold, including subsets in the Chinese PDF and the Chinese plot | SIL Open Font License 1.1. The original font files are fetched at commit `9b0f1436e455d902de067a2501422e5dc71ad16b` and verified by digest. [Pinned upstream license](https://github.com/notofonts/noto-cjk/blob/9b0f1436e455d902de067a2501422e5dc71ad16b/Serif/LICENSE) · [unaltered notice](notices/Noto-OFL.txt) |
| Computer Modern Type 1 and MSBM math fonts supplied by AMSFonts | The AMSFonts distribution identifies its Type 1 fonts as OFL. Copyright and reserved font names are preserved in the supplied text. [AMSFonts README](https://ctan.math.illinois.edu/fonts/amsfonts/README) · [unaltered AMS notice](notices/AMS-OFL.txt) |
| Latin Modern Roman and Mono | GUST Font License 1.0 under the conditions of LPPL 1.3c or later. The Latin Modern project credits B. Jackowski and J. M. Nowacki on behalf of TeX Users Groups. [Latin Modern README](https://ctan.math.illinois.edu/fonts/lm/README) · [unaltered GUST notice](notices/LM-GFL.txt) · [LPPL 1.3c](notices/LPPL-1.3c.txt) |

Both pinned Noto font files identify their copyright as © 2017–2024 Adobe. The release preserves the accepted PDFs, including the embedded subsets, and the raster figures. The downloadable font programs are external build inputs. The notices accompany the release assets. The OFL project's FAQ explains embedding in documents and the separate status of the surrounding text. [OFL FAQ, document embedding](https://openfontlicense.org/ofl-faq/)

## External build and verification dependencies

The following packages are obtained by the reader. Their source trees, build caches, installed wheels, toolchains and the TeX bundle are outside this repository and its release assets.

- Lean 4.28.0 carries Apache-2.0 and notices for its bundled components. Of the nine exact Lake checkouts, mathlib, plausible, LeanSearchClient, importGraph, ProofWidgets4, aesop, Qq and batteries carry Apache-2.0; Cli carries MIT. These identifications come from the LICENSE files at the revisions in the upstream manifest. [Lean toolchain](https://github.com/leanprover/lean4/tree/v4.28.0) · [pinned Lake manifest](https://github.com/xiujiang4/alternating-particle-chains/blob/3389797a4aac8ed1c65e93c864cfa2305b65359a/lean/lake-manifest.json)
- The plotting environment is installed from the eleven exact [PyPI requirements](study/figure-requirements.txt). The wheel metadata and included notices identify BSD-family terms for contourpy, cycler, kiwisolver and python-dateutil; MIT for fonttools and pyparsing; MIT-CMU for Pillow; Apache-2.0 or BSD-2-Clause for packaging; Apache-2.0 for tzdata. NumPy includes its BSD terms and component notices. Matplotlib provides its own license agreement and component notices. Fonttools also supplies separate external notices. These are descriptions of the tested distributions. Their complete packaged notices govern their respective components.
- Tectonic 0.17.0 runs the v33 TeX bundle. TeX packages and fonts carry their own licenses. The bundle's verified identifier is in the [frozen reproduction guide](study/README.md). [Tectonic release](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0)

The v1.0.1 publication boundary is the original research files, the accepted document outputs and separately identified notices. Vendoring historical modules or assigning a new project license would require its own rights decision.
