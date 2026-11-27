# Alternating Gaussian chains · Lean 4

论文 v1.0.1 的六项编号结果已全部通过 Lean。范围、直接依赖、声明名称和冷重建记录见[逐项验收表](RESULTS.md)。[公理审计入口](Axioms.lean) 与[实际输出](AXIOMS.txt) 可逐项对照。

All six numbered results have Lean proofs. To review them, start with the statements and their hypotheses, then follow the certificate soundness proofs before reading individual generated boxes.

| Review target | Entry points |
|---|---|
| Energy normalization and the four-site bridge | [Physical energy](ChainEnergy.lean) · [Fourier identity](ChainFourier.lean) · [Four-site comparison](FourBridge.lean) |
| Theorem 1, Corollary 2, Theorem 3 and Proposition 4 | [Exact cluster locking](ClustersLock.lean) · [Two-site case](ClustersTwo.lean) · [Minimum energy expansion](ClusterSeriesTheorems.lean) · [Closed face](PackedFaceTheorem.lean) · [Bifurcation](BifurcationProposition.lean) |
| Theorems 5 and 6 on the full feasible domain | [Width strip](StripTheorem.lean) · [Isolated parameter pair](Point22Theorem.lean) |
| How finite data implies a statement about real configurations | [Closed-box checker](CertTree.lean) · [Strip leaf and split proofs](BandLocalProof.lean) · [Width-22 atlas](Point22AtlasFull.lean) · [Root and sign-reversal test](CertRoot.lean) |

| 输入 | 固定版本 |
|---|---|
| 论文与附件 | v1.0.1，`9a1909592c7131c12ddc176fbe153e442fbe0362` |
| 本工程引用的上游 Lean 定义 | `4c92f3aea0bd43931001f12f660b43e5d3ccb628`，含 PR #7 |
| 复跑原论文 Python 附件的上游输入 | `3389797a4aac8ed1c65e93c864cfa2305b65359a`，按原 SHA-256 清单提取 |
| Lean / Lake | Lean 4.28.0，编译器提交 `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`；Lake 5.0.0-src+7e01a1b |
| mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365`，v4.28.0 |

## 从干净副本重建

Use a full Git checkout containing this directory, Python 3.11 or later, and `elan` with its `lean` and `lake` commands on PATH. Run from the repository root. The driver restores the pinned upstream source and toolchain file, checks the dependencies, builds the default Lake target and audits the declared axioms.

```sh
cd formalization
python rebuild.py
```

`setup.py` 默认从公开上游取得固定提交的 14 个 Lean 模块、工具链文件及 Lake manifest，并从本仓库的冻结 Git 对象恢复 `AlternatingMoments.lean`。已有上游完整副本时，可向 `rebuild.py` 提供 `--upstream-git PATH`。本文使用上表列出的固定版本。[输入恢复脚本](setup.py) · [原始权属记录](../THIRD-PARTY.md)

`rebuild.py` 在项目自己的 `.lake/build` 为空时运行。它获取所需第三方 mathlib 缓存、核对 manifest 中每个包的 Git revision、执行默认 Lake 构建，再核对所有预期的公理报告。已准备好固定版本的第三方 `.lake/packages` 时可加 `--installed-dependencies`。脚本默认按依赖顺序每批构建两个模块，再运行同一个 Lake 默认目标。可用 `--batch-size` 调整并行批次。构建完成后可用以下命令独立复核。

```sh
lake build
lake env lean Axioms.lean
```

## 中断后续跑

保留当前副本的 `.lake/build` 和 `.lake/packages`。源码与证书输入保存在 Git 中。每个核验分片的 Lean 对象和构建记录分别保存在 `.lake/build/lib/lean/*.olean` 和同名的 `.trace`。Windows 重启后，在原来的 `formalization` 目录用 PowerShell 7 运行以下命令。脚本使用 PATH 中的 Python 和 Lean 工具链，补建缺失模块，然后运行默认目标和公理审计。

```powershell
.\resume.ps1
```

已有上游 Git 副本时，Windows 脚本接受 `-UpstreamGit PATH`。其他平台可运行 `python rebuild.py --resume`。完整冷重建使用上文的干净副本命令。

## 证书重建与信任边界

在同一目录运行以下命令。

```sh
python replay_certificates.py --work-dir ../../chain-replay
```

工作目录由冻结包的 setup 命令创建。脚本复跑原论文的 15 个验证程序及 16 个附录，并重新生成有限数据。在条带排除中，三个区间共有 2,016 个「间距区间、相对支撑」组合。生成器记录每棵候选树的分裂坐标、切点、试探、叶类型与中点，并生成含中间整数盒的 Lean 节点证明。Lean 检查器的起始盒由物理参数与支撑编号决定。数据生成、树覆盖、实数核包围与最终全域声明是不同步骤，具体通过的步骤见[验收表](RESULTS.md)。

数值公理审计覆盖有理数、向外舍入、Gaussian 核与导数的有限和及尾界、连续盒覆盖、端点变号和已接入的实际证书。普通 `decide` 和 `decide +kernel` 产生 Lean 可核验的证明。Python 转录、摘要和本机原生程序输出仅用于再生输入与交叉检查。
