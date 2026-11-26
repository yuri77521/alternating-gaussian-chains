# Response to the independent referee · v1.0.1

**Research coordination: yuri77521**<br>
**AI research: OpenAI Codex (GPT-6.2 Astra)**<br>
Independent Research Project

本文回覆 2026-11-26 對雙語送審稿的獨立 AI 審查。下列路徑均以解壓後的研究附件為準。六項編號結果沿用送審稿的陳述、假設與適用區間。數值驗收資料見 [證書記錄](logs/certificates.txt)、[補充見證與探索記錄](logs/experiments.txt) 和 [Lean 公理記錄](logs/axioms.txt)。

## 三項重大意見

| 意見 | 本次修改 | 驗收證據 |
|---|---|---|
| M1．公開附件缺少誤差半徑和取整常數的推導 | 匯出 19 份可執行附錄時連同數學文字一併保留，另附完整取整推導。證據索引從 16 模截斷、定點外捨入和係數傳播推到能量半徑 $10^{-42}$、係數半徑 $10^{-34}$ 及四階商半徑。沿取整配置對間距下限微分，頂點速度與中心速度的平方差和分別為 105 和 24。 | [誤差預算](EVIDENCE.md#error-budgets-in-the-executable-notes) · [原頻域見證及推導](research/exact-clusters/certificate-referee.md) · [取整證明](research/six-site/global-probe.md)。低、高兩段的排除餘量分別大於 $3695922\cdot10^{-9}$ 和 $791864\cdot10^{-9}$。 |
| M2．「首次失優」可能把開集的下確界寫成最小元 | 在 $h=1/1000$ 固定時定義 $D(s)=\min_F E_s-\min_K E_s$ 及 $s_*=\inf\{s>9:D(s)>0\}$。$F,K$ 固定且緊，$D$ 連續，$D(9)=0$、$D(22)>0$。嚴格落敗的寬度構成開集。正文、分發指南與證據索引均以 $s_*$ 表述，另列邊界共存問題。 | [雙語結論 §7](manuscript/paper/evidence.tex) · [指南](README.md) · [證據索引](EVIDENCE.md) · [來源表](SOURCES.md)。定理 5 的條帶與定理 6 的單點條件沿用原文。 |
| M3．首頁及 PDF 元資料仍有署名佔位符 | 在中英文首頁、PDF Author 欄及本版引用資料使用上列三行署名。 | [共用署名定義](manuscript/paper/article.tex) · [英文 PDF](paper-en.pdf) · [繁體中文 PDF](paper-zh.pdf)。核對首頁文字及兩個獨立的 PDF Author 欄。 |

## 四項輕微意見

| 意見 | 本次修改 | 驗收證據 |
|---|---|---|
| m1．寬度條帶的核表算法描述 | 附錄 A 說明得分中點採最近節點的一階 Taylor 近似。網距 $1/M$ 下，距離至多 $1/(2M)$，二階餘項至多 $\|G''\|_\infty/(8M^2)$；節點值、斜率及向下取整的誤差另計。寬度 22 的塊核仍採其原有插值。 | [附錄 A](manuscript/paper/evidence.tex) · [Band._at 與 center_value](code/verify_six_site_global_reduction.py)。三段條帶訪問盒數為 6,068、40,740、39,056。 |
| m2．$s=22$ 見證須就地標出前例 | 在定理 6 的證明首次寫出 $X$ 時，說明它來自 PR 1 式 (17)，第三個坐標由 $125/1000$ 移至 $126/1000$。論文分別說明早期的極限偶極比較、本稿的整面比較及全部極小者分類。 | [定理 6 證明](manuscript/paper/point.tex) · [PR 1 固定原稿](https://github.com/Kemody/alternating-particle-chains/blob/7b9bc3e1b13d398a1bf54ab340c18cd3c8f3c88c/en/gaussian-infimum.md)。兩個語言分支均在同一處引用式 (17)。 |
| m3．補記上游 PR 7 | 正文及來源表加入四粒子連續位移族的 Lean 比較。位移滿足 $0<\lvert t\rvert<1$，寬度條件為 $0<q\le1/4$。前作的固定比較、其後的連續位移結果、本稿四項矩與間隙導數聲明各自標明。 | [引言](manuscript/paper/model.tex) · [文獻表](manuscript/paper/references.tex) · [固定版本與聲明](SOURCES.md)。本次編譯對象仍為固定的基礎專案及本稿矩文件。 |
| m4．中文圖 1 圖內文字 | 使用同一組有理根括區與階梯邊界，另繪繁體中文標題、分圖、兩軸、均勻端點與四項圖例。 | [英文圖](research/six-site/width-strip.png) · [中文圖](research/six-site/width-strip-zh.png) · [繪圖程式](code/plot_six_site_width_strip.py)。兩圖均使用 33 個寬度節點，分語言載入 PDF。 |

## 三項改進建議

1. **定點附近的相型。** 採納「顯式邊界」的限定。§7 說明定理 6 處理認證的參數點，周圍相區的顯式範圍仍待確定。本版未新增鄰域定理、寬度區間或延拓數值。[結論](manuscript/paper/evidence.tex)
2. **復算須核對數值內容。** 數值入口逐行核對主證書、兩組取整證書和補充有理見證；投影搜索的浮點軌跡可因平台而異。結果寫入 `results/strict-checks.txt`。Lean 另行核對六項聲明名稱與公理集合。[數值入口](reproduce.py) · [Lean 入口](reproduce_lean.py)
3. **文獻檢索範圍。** 來源表補錄既有檢索日期、OpenAlex 引文追蹤、上游截點、Issue 5 與 PR 7 的獨立版本，並補記圓周重排的歷史來源；優先權比較限於當時保存的記錄。[來源與歸屬](SOURCES.md)

[復現報告](Reproduction.md) 列出乾淨副本的檢查、數值內容核對及製品雜湊；ZIP 自身的 SHA-256 與最終重放回執隨包提供。包內 `REVISION.txt` 標識該次來源提交。
