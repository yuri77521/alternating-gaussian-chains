"""Draw the six-site phase diagram from rational root brackets (Matplotlib)."""

import argparse
from fractions import Fraction as F
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
from matplotlib.patches import Patch, Rectangle

from verify_six_site_strip_thresholds import root_bracket


FIGURE = Path(__file__).resolve().parents[1] / "research/six-site/width-strip.png"


def phase_bands(widths):
    # Both thresholds decrease. The right lower and left upper root bounds
    # therefore enclose a whole continuous curve segment, including its ends.
    center = [root_bracket(s, False, digits=9) for s in widths]
    contact = [root_bracket(s, True, digits=9) for s in widths]
    bands = [[], [], [], []]
    for i in range(len(widths)-1):
        limits = center[i+1][0], center[i][1], contact[i+1][0], contact[i][1]
        assert 0 < limits[0] < limits[1] < limits[2] < limits[3] < F(1, 6)
        for band, value in zip(bands, limits):
            band.append(float(value))
    return [band + [band[-1]] for band in bands]


def draw(path, language="en", font_dir=None):
    chinese = language == "zh"
    style = {}
    bold = {}
    if chinese:
        regular = font_dir / "NotoSerifCJKtc-Regular.otf"
        heavy = font_dir / "NotoSerifCJKtc-Bold.otf"
        style = {"fontproperties": FontProperties(fname=str(regular))}
        bold = {"fontproperties": FontProperties(fname=str(heavy))}

    widths = [8 + F(k, 32) for k in range(33)]
    x = [float(s) for s in widths]
    c_lo, c_hi, b_lo, b_hi = phase_bands(widths)
    floor_min, floor_max = 0.1255, 0.1345
    colors = ("#bedfd7", "#f7cb89", "#cfdaeb")
    boundary = "#526074"
    fig, axes = plt.subplots(1, 2, figsize=(10.6, 4.8), width_ratios=(1, 1.55))
    fig.subplots_adjust(left=.085, right=.975, top=.81, bottom=.23, wspace=.30)
    for ax in axes:
        for lower, upper, color in (
                (0, c_lo, colors[0]), (c_lo, c_hi, boundary),
                (c_hi, b_lo, colors[1]), (b_lo, b_hi, boundary),
                (b_hi, 1/6, colors[2])):
            ax.fill_between(x, lower, upper, step="post", color=color, linewidth=0)
        ax.set_xlim(8, 9)
        ax.set_xticks([8, 8.25, 8.5, 8.75, 9], ["8", "8.25", "8.5", "8.75", "9"])
        ax.set_xlabel(r"高斯寬度 $s=\alpha L^2$" if chinese else r"Gaussian width $s=\alpha L^2$", **style)
        ax.set_axisbelow(True)
        ax.tick_params(length=3, color=boundary)
        ax.spines[["top", "right"]].set_visible(False)
    axes[0].set_title("全部可行正下限" if chinese else "Full range of positive floors", loc="left", **style)
    axes[0].set_ylabel(r"最小間距 $h=h_{\rm phys}/L$" if chinese else r"Minimum spacing $h=h_{\rm phys}/L$", **style)
    axes[0].set_ylim(0, 1/6)
    axes[0].set_yticks([0, .04, .08, .12, 1/6], ["0", "0.04", "0.08", "0.12", "1/6"])
    axes[0].axhline(1/6, color=boundary, lw=1.5)
    axes[0].text(8.04, .162, "均勻構型（1/6）" if chinese else "Uniform at 1/6", va="top", fontsize=9, color="#334359", **style)
    axes[0].add_patch(Rectangle((8, floor_min), 1, floor_max-floor_min,
                                fill=False, ls="--", lw=1.1, edgecolor=boundary))
    axes[1].set_title("相變區放大圖" if chinese else "Transition region (enlarged)", loc="left", **style)
    axes[1].set_ylim(floor_min, floor_max)
    axes[1].set_yticks([.126, .128, .130, .132, .134])
    fig.suptitle("六粒子交替高斯鏈" if chinese else "Six-site alternating Gaussian chain", x=.085, ha="left",
                 fontsize=17, fontweight="semibold", **bold)
    labels = (("對徑雙三簇", "偏移雙三簇", "五接觸", "臨界曲線的認證包圍帶") if chinese else
              ("Antipodal triples", "Shifted triples", "Five contacts", "Certified threshold enclosure"))
    legend = [Patch(color=c, label=name) for c, name in zip((*colors, boundary), labels)]
    fig.legend(handles=legend, ncol=4, loc="lower center", frameon=False, handlelength=1.3, prop=style.get("fontproperties"))
    fig.savefig(path, dpi=170, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="destination PNG (language-specific by default)")
    parser.add_argument("--language", choices=("en", "zh"), default="en")
    parser.add_argument("--font-dir", type=Path, help="pinned regular and bold CJK font directory")
    args = parser.parse_args()
    if args.language == "zh" and args.font_dir is None:
        parser.error("--language zh requires --font-dir")
    default = FIGURE.with_name("width-strip-zh.png") if args.language == "zh" else FIGURE
    draw(args.output or default, args.language, args.font_dir)
