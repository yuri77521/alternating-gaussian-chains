# 论文与 Lean 声明对应表

目标是已发布的 v1.0.1。归一化量为 xⱼ=Xⱼ/L、s=αL²、q=exp(−π²/s)、c=√(π/s)。间隙下限 h 按周期归一化，η=2πh 是角间距。全部 N 个间隙之和为 1，包括跨周期的最后一个间隙。h=0 的闭可行域允许碰撞，严格有序类要求每个间隙大于零。表中“已验证”表示 Lean 声明已成功编译，并已核对其公理报告。[间隙与周期提升](ChainGeometry.lean)

| 编号 | Lean 声明及证明源文件 | 直接依赖 | 适用范围与验收结论 |
|---|---|---|---|
| §2 式 (1)–(2) | [physicalEnergy_eq_imageEnergy](ChainEnergy.lean)、[physicalEnergy_fourier](ChainFourier.lean)、[product_tsum_fourier](DirectedImages.lean) | `ChainEnergy`、`KernelFourier`，含移位 theta 恒等式、绝对收敛、有限对换序及电中性 | 已验证。任意正偶数粒子数、α>0、L>0；允许不同标签重合。只删除同标签的中央周期像。各阶真实空间导数的 Fourier 级数在紧正宽度区间及所有位移上一致绝对收敛。[一致收敛声明](ChainUniform.lean) |
| 四粒子桥接 | [physicalEnergy_four_eq_cellEnergyAt、imageEnergy_four_quarter、imageEnergy_four_displacement_lt](FourBridge.lean) | `ChainEnergy`、上游 `GaussianDisplacementEnergy` | 已验证。N=L=4、s=16a。四个坐标互异时接到 `AlternatingChains.Fourier.cellEnergyAt`，再由 `cellEnergyAt_quarter` 接回原定义。PR #7 的位移不等式沿用其 nome 与位移条件。 |
| 定理 1 | [exact_cluster_locking、cluster_ground_state_representatives](ClustersLock.lean)、[two_site_classification](ClustersTwo.lean) | `ClustersLocalizedCut`、`ClustersLockedChart`、`ClusterSeriesLocking`、`ClusterSeriesOrbitsSwap` | 整条已验证。N=2m≥4、R(q)≤2/3、0<η≤1/[N(1+3πm²)²]。两紧奇簇平衡、对径，保号轨道数随簇长是否相等而定。N=2 单独覆盖每个可行下限。 |
| 推论 2 | [corollary_two_exact、corollary_two_fourth、corollary_two_pair_polynomial](ClusterSeriesTheorems.lean) | `ClustersLock`、`ClusterSeriesTwo` | 整条已验证。对全可行域的最低能量给出精确级数与 η=2πh→0⁺ 的四阶展开。不等长簇的偶频项保留，求和余项为 O(η⁶)。 |
| 定理 3 | [theorem_three、closed_face_all_nomes](PackedFaceTheorem.lean) | `PackedFaceEnergyTable`、`PackedFaceBoundsThresholdAnalytic`、`PackedFaceReflection` | 整条已验证。0<q≤17/50，紧双三簇闭面，含 h=h_c、h=h_b 及 h=1/6。两根的唯一性、简单性、解析性、单调性及全部极小位移均进入声明。 |
| 命题 4 | [proposition4](BifurcationProposition.lean)、[临界根和导数包围](BifurcationCritical.lean) | `BifurcationMinimizers` | 整条已验证。s=8，在固定平移后的完整可行域，居中态于 0<h≤h_c 为严格局部极小，于 h_c<h<1/6 为受约束鞍点。两个分支各自的平方根律、能量增益与系数均获证。 |
| 定理 5 | [theorem_five](StripTheorem.lean)、[全域归约](StripTheoremAssembly.lean)、[phaseWidth_deriv_bounds](PhaseStripVerified.lean) | `StripTheoremAssembly`、`BandRowsVerified` | 整条已验证。2,016 棵树覆盖 85,864 个节点，包括全部面外支撑。两段小间距、十个根区间、32 段相宽导数、碰撞闭包及两个阈值的端点一并验收。 |
| 定理 6 | [theorem6、unique_root_gives_all_ground_states](Point22Theorem.lean)、[独立两树入口](Point22TwoTreesComplete.lean) | `Point22FromAtlas`、`Point22Consequences`、`Point22TwoTreesComplete`、`CertRootSimple` | 整条已验证。编号定理、十类解析排除加两树的分类、独立十二树复核均通过冷重建。 |
| 证书可靠性 | [accept_sound、bracket_sound](CertTree.lean)、[插值误差](CertTreeInterpolation.lean)、[空间查询](CertTreeStripCache.lean)、[逐盒排除](BandLocalProof.lean) | 有理数向外舍入、无限高斯尾、导数级数、闭盒覆盖和候选极值的必要条件 | 通用定理及真实示例已验证。[改坏端点符号](CertRoot.lean) 与[删除必要子盒](CertTreeAtlasExample.lean) 均被拒绝。[能量排除盒](CertRootWitness.lean) 还给出被删除的半盒内确有可行构型。 |

定理 1 的宽度界包括 s=9。半圆亏损在 Lean 中通过对称差的积分估计和逐个 Fourier 模式的界来证明。论文四条奇簇矩声明通过角坐标与实际周期间隙接入一般构型。[宽度界](ClustersWidth.lean) · [半圆亏损](ClustersLocalizationPhysical.lean) · [坐标与簇矩桥接](ClustersGeometry.lean)

定理 6 的试探比较与全域结论分别验收。前者给出一个可行构型严格胜过整条紧面；后者解析排除九种双接触类型和全松隙类型，再通过余下 21111、3111 的 2,828 个节点及所需的 1,055 项连续区间界完成定位与唯一性证明。[整面严格比较](CertRootFace.lean) · [全域物理接线](Point22TwoTreesComplete.lean)

在 [8,9] 上，相宽 Δ=h_b−h_c 满足严格界 `0.000209555 < Δ′(s) < 0.000734655`。[闭条带导数界](PhaseStripVerified.lean)

在 (22,1/1000) 处，最优间隙为 `(h,h,R−h,1/2−R,1/2−R,R−h)` 的循环移位。R 与最低能量 M₆ 同时满足以下严格不等式。

```text
0.249999032167246504146498709394 < R < 0.249999032167246504146498709395
0.66503584451339086827047430 < M₆ < 0.66503584451339086827047431
```

另一条独立路径检查了全部十二棵原树、5,638 个节点及 1,080 个区间查询。32,000 个空间点的零至二阶导数共 192,000 个端点均有内核证明。由此同样能把每一个真实全局极小者定位到 3111 局部唯一性区域。[十二词全域定位](Point22AtlasFull.lean)

冻结 Python 入口恢复 73 个包内文件与 17 个旧上游输入，运行 15 个 verifier 与 16 个附录，243 行严格输出与归档相符。生成器提供候选树、端点和见证。Lean 通过数学可靠性定理和 `decide +kernel` 等内核可核验的证明检查实际内容。[重建命令](README.md) · [集中公理审计](Axioms.lean)

## 最终验收记录

公开源码提交 `1a291b82d487bce3b412a76023df6d9116cea620` 中，受版本控制的 1,126 个 Lean 文件、Lake 配置和证书输入已与通过冷重建的版本逐项比对，Git blob 完全一致。独立 Windows x86-64 验收副本从空的项目构建目录开始，只预置固定第三方包，九个包均核对了 Git revision 及已跟踪源码。Lean 为 4.28.0，编译器提交为 `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`。全部项目对象都在该独立副本中编译。

- 全部 1141 个项目模块均有 Lake 构建产物。计算密集的分片先按依赖分组，然后运行 `lake --no-cache build`。默认目标退出码为 0，Lake 报告 4085 个构建条目，包含依赖。
- `lake env lean Axioms.lean` 独立审计了 62 条声明。六项编号结果和一般能量、四粒子桥、通用证书检查定理的公理集合均为 `propext`、`Classical.choice`、`Quot.sound`。[原始输出](AXIOMS.txt)
- `python replay_certificates.py --work-dir ../../chain-replay` 可复跑冻结原件并重新生成候选数据。区间结论依靠已审计的 Lean 定理。
- 中断恢复另在 232 模块、51 条审计的检查点实测通过。重新运行保留已验收分片的内容和修改时间。[恢复命令](README.md)
