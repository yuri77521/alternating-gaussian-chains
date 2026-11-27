# Alternating Gaussian chains

**Research coordination: yuri77521**<br>
**AI research: OpenAI Codex (GPT-6.2 Astra)**<br>
Independent Research Project

[English paper (PDF)](study/paper-en.pdf) · [繁體中文論文 (PDF)](study/paper-zh.pdf) · [Theorem and evidence index](study/EVIDENCE.md) · [v1.0.1 release notes](RELEASE-NOTES.md)

This study asks which configurations minimize the energy of a periodic one-dimensional chain of alternating charges when every gap has a positive lower bound. For a fixed even particle count, explicit width and small-gap conditions force two packed odd clusters with antipodal midpoints. For six particles, all minimizers are classified for every feasible positive floor throughout the normalized width strip $7.99\le s\le9$. At the separate pair $(s,h)=(22,1/1000)$, the minimizing geometry is one packed triple plus three singletons.

繁體中文論文與英文版使用相同的定理、公式及圖表編號。六粒子的全域結論結合解析證明與嚴格區間證書。v1.0.1 發布時隨附的 Lean 檔案檢查兩項一般奇數簇矩恆等式及兩項三粒子方差與間隙導數聲明。原有的四粒子形式化與其來源另列於文獻及證據索引。

## Lean proofs of the six results

The post-release Lean 4 development verifies all six numbered results of v1.0.1. It starts from the ordered energy per particle, recovers the four-site model, and checks the continuous-domain certificates for the six-site classifications. The 62 audited declarations each report `propext`, `Classical.choice` and `Quot.sound`. [Theorems and hypotheses](formalization/RESULTS.md) · [Build and review guide](formalization/README.md) · [Axiom transcript](formalization/AXIOMS.txt)

發布後的形式化涵蓋六項編號結果。定理 5 在整個寬度條帶分類全部可行六粒子構型的極小者。定理 6 的分類與數值包圍只適用於 $(s,h)=(22,1/1000)$。[定理 5](formalization/StripTheorem.lean) · [定理 6](formalization/Point22Theorem.lean)

## Read and reproduce

The [study directory](study/) contains the 73 files of the frozen v1.0.1 research package. Its [manifest](study/SHA256SUMS.txt) covers the paper sources, PDFs, executable proof notes, interval programs, formal statements and reference logs. The [revision record](study/REVISION.txt) identifies the historical manuscript snapshot. The public Git tag identifies this independently initialized distribution.

With CPython 3.12, Git, elan, Lean 4.28.0 and Tectonic 0.17.0 installed, run from the repository root with a new sibling working directory:

```sh
python -m venv .venv
# Activate the environment, or invoke its Python directly.
python -m pip install -r study/figure-requirements.txt
python -B study/reproduce.py all --work-dir ../chain-replay
```

The driver downloads 17 hash-checked source/build files from the public upstream, including all 12 baseline Lean modules, then resolves the nine pinned Lake packages. The four odd-cluster statements are in [AlternatingMoments.lean](study/research/exact-clusters/AlternatingMoments.lean). Both language editions use pinned Noto fonts and the Tectonic v33 typesetting bundle. The complete run writes checks, figures, documents and Lean output to the work directory. For just the numerical certificates use `numeric` in place of `all`; this part needs only Python's standard library and the downloadable historical source inputs.

See the [reproduction guide](study/README.md), [standalone verification](VERIFICATION.md), [frozen reproduction report](study/Reproduction.md) and [point-by-point referee response](study/Response-to-Reviewer.md). The [sources](study/SOURCES.md) identify the earlier collision results, four-site work, and the separate scope of the new six-site classifications. The [rights and dependency notes](THIRD-PARTY.md) describe the distribution boundary.

## Citation and research roles

Use [CITATION.cff](CITATION.cff) for the versioned citation and the [contribution statement](AI-CONTRIBUTIONS.md) for research roles and verification scope. The papers are research manuscripts.
