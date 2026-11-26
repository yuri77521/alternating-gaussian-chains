# Exact clusters and global transitions in periodic alternating Gaussian chains with a minimum spacing

**Research coordination: yuri77521**<br>
**AI research: OpenAI Codex (GPT-6.2 Astra)**<br>
Independent Research Project

[English paper](paper-en.pdf) · [繁體中文論文](paper-zh.pdf) · [Theorem and evidence index](EVIDENCE.md) · [Sources and attribution](SOURCES.md) · [Response to the referee](Response-to-Reviewer.md) · [Reproduction report](Reproduction.md) · [Complete file list](FILES.txt)

The articles treat exact cluster locking at small positive spacing for fixed even particle count under an explicit width condition. At six sites the global classification covers every feasible positive floor throughout the width strip [7.99, 9]. The triple-plus-three-singleton classification holds at the separate parameter pair (22, 1/1000). At $h=1/1000$, write $D(s)$ for the minimum on the closed packed-triple face minus the minimum on the full simplex. The lower boundary of the strict-defeat set is $s_*=\inf\{s>9:D(s)>0\}$. Its value and possible coexistence there remain undetermined.

兩份論文共用定理、公式、圖表及文獻編號。從各定理可經證據索引查到嚴格區間證書、解析證明、Lean 聲明及另列的探索實驗。在固定下限 $h=1/1000$ 時，待求的是緊面能量嚴格高於全域最小值之寬度集合的下確界。前作按固定版本引用，其必要檔案於復算時讀入獨立工作目錄。

## Reproduce from a clean extraction

Extract the ZIP into a new directory, open a shell there, and use CPython 3.12 (tested with 3.12.10), Git, Tectonic 0.17.0 with its v33 bundle and elan with the Lean 4.28.0 toolchain. The plotting package versions in [figure-requirements.txt](figure-requirements.txt) reproduce both reference PNGs on Windows x86-64. Install them in a new Python environment. With that environment active, run:

```sh
python -m pip install -r figure-requirements.txt
elan toolchain install leanprover/lean4:v4.28.0
python -B reproduce.py all --work-dir ../chain-replay
```

The driver checks the distributed file hashes, then assembles the research inputs in a new sibling directory. On first use it obtains the two historical Python files and the 12 Lean modules plus three build files from their fixed upstream snapshot. Every external file is checked against [upstream-files.sha256](upstream-files.sha256). Lake uses the nine exact package revisions in the upstream manifest. Tectonic uses its v33 bundle and the two hash-checked static faces of Noto Serif CJK TC. The font commit is `9b0f1436e455d902de067a2501422e5dc71ad16b`. The reference bundle content identifier is `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`. [Tectonic release](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0) · [Font source and license](https://github.com/notofonts/noto-cjk/tree/9b0f1436e455d902de067a2501422e5dc71ad16b/Serif)

The individual commands accept the same `--work-dir`: `setup` verifies and assembles the inputs, `numeric` replays the 11 certificate and experiment groups, `artifacts` regenerates the figure and both papers, and `lean` rebuilds all project modules and checks the precise axiom sets of six declarations. `all` runs these stages in order. For another clean Lean build choose a new work directory. All new output is written under the work directory. The plotting interpreter can be selected with `--figure-python PATH`. Each computational check writes a transcript under `results/`; the reference transcripts are in [logs/](logs/). The two archived PDFs and both figures are compared byte for byte. Different builds of the fonts, raster or compression libraries may produce a byte mismatch. Floating searches can vary across platforms. The rational bounds, coverage checks and accepted Lean declarations are identified separately in [EVIDENCE.md](EVIDENCE.md).

## Replay with local dependency copies

For a machine with the toolchains and dependency caches already installed, replace the example paths below with the locations of the local inputs. The Git repository must contain commit `3389797a4aac8ed1c65e93c864cfa2305b65359a`. Its checked-out branch is immaterial. The driver reads only the pinned Git blobs. The font directory must contain `NotoSerifCJKtc-Regular.otf` and `NotoSerifCJKtc-Bold.otf` from the cited revision.

```sh
python -B reproduce.py setup --work-dir ../chain-replay --upstream-git ../upstream
```

For offline Lean builds, populate only `../chain-replay/lean/.lake/packages` with the nine version-matched dependency checkouts and their third-party build caches. Start with zero compiled objects under `../chain-replay/lean/.lake/build`. Add elan, Tectonic and Git to PATH. For Git for Windows tar, set `LANG=C.UTF-8`, `LC_ALL=C.UTF-8` and `TAR_OPTIONS=--force-local` when fetching a new dependency cache. Then use the local plotting environment and the existing v33 Tectonic cache:

```sh
python -B reproduce.py all --work-dir ../chain-replay --upstream-git ../upstream --installed-dependencies --only-cached --font-dir ../fonts --figure-python ../plot-env/bin/python
```

On Windows the plotting interpreter in a virtual environment is `../plot-env/Scripts/python.exe`. The master interval replay runs 15 certificate programs and 16 proof appendices. The supplementary replay runs three additional executable witnesses. Each executable appendix includes its mathematical notes and the original program. The rounding proof is also distributed. Numeric replay compares the master certificate, both rounding transcripts and the supplementary rational witnesses with their archived output. The checks are listed in results/strict-checks.txt. Floating search trajectories remain platform-dependent. Definitions, hypotheses and the arguments relating the checks to global conclusions appear in the papers. The figure uses 33 rational widths and certified enclosures between them.

The archive records its source commit in [REVISION.txt](REVISION.txt). [SHA256SUMS.txt](SHA256SUMS.txt) covers every other file, including the file list. The prior papers, scripts and formal development are identified by version in [SOURCES.md](SOURCES.md).
