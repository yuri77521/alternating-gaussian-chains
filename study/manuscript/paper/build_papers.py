"""Build the English and Chinese articles from a staged copy with pinned CJK fonts."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.request import urlopen


SOURCE = Path(__file__).resolve().parent
FIGURES = [Path("research/six-site") / name for name in ("width-strip.png", "width-strip-zh.png")]
FONT_SOURCE = (
    "https://raw.githubusercontent.com/notofonts/noto-cjk/"
    "9b0f1436e455d902de067a2501422e5dc71ad16b/Serif/OTF/TraditionalChinese/"
)
FONT_HASHES = {
    "NotoSerifCJKtc-Regular.otf": "234301038e76e7c35c43113785024700c4e4fe7bdce1d1fbbc42fca7e6683798",
    "NotoSerifCJKtc-Bold.otf": "a4441a76dbf56719600c5dcbd5b5e5a068a20944cc41c959487a657133576ee6",
}
BUNDLE = "https://relay.fullyjustified.net/default_bundle_v33.tar"


def stage_fonts(destination, font_dir):
    destination.mkdir()
    for name, digest in FONT_HASHES.items():
        target = destination / name
        if font_dir:
            shutil.copyfile(font_dir / name, target)
        else:
            with urlopen(FONT_SOURCE + name, timeout=120) as remote, target.open("wb") as local:
                shutil.copyfileobj(remote, local)
        with target.open("rb") as font:
            actual = hashlib.file_digest(font, "sha256").hexdigest()
        if actual != digest:
            raise ValueError(f"SHA-256 mismatch for {name}: {actual}; expected {digest}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True, help="directory for the two finished PDFs")
    parser.add_argument("--font-dir", type=Path, help="use the two official static OTF files from this directory")
    parser.add_argument("--engine", choices=("tectonic", "xelatex"), default="tectonic")
    parser.add_argument("--only-cached", action="store_true", help="use only cached Tectonic bundle resources")
    parser.add_argument("--keep-logs", action="store_true", help="also copy the .log and .aux files for auditing")
    args = parser.parse_args()
    if args.only_cached and args.engine != "tectonic":
        parser.error("--only-cached requires --engine tectonic")
    engine = shutil.which(args.engine)
    if not engine:
        parser.error(f"{args.engine} was not found on PATH")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH="1795651200", FORCE_SOURCE_DATE="1", TZ="UTC")
    with tempfile.TemporaryDirectory(prefix="gaussian-chain-tex-") as temporary:
        root = Path(temporary)
        work = root / "manuscript" / "paper"
        work.mkdir(parents=True)
        for tex in SOURCE.glob("*.tex"):
            shutil.copyfile(tex, work / tex.name)
        for figure in FIGURES:
            (root / figure.parent).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SOURCE.parents[1] / figure, root / figure)
        stage_fonts(work / "fonts", args.font_dir)
        for language in ("en", "zh"):
            stem = f"paper-{language}"
            if args.engine == "tectonic":
                command = [engine, "--bundle", BUNDLE, "--keep-logs", "--keep-intermediates"]
                if args.only_cached:
                    command.append("--only-cached")
                command.append(stem + ".tex")
                subprocess.run(command, cwd=work, env=env, check=True)
            else:
                command = [engine, "-no-shell-escape", "-halt-on-error", "-interaction=nonstopmode", stem + ".tex"]
                for _ in range(2):
                    subprocess.run(command, cwd=work, env=env, check=True)
            log = (work / (stem + ".log")).read_text(encoding="utf-8", errors="replace")
            failures = ("Missing character:", "There were undefined references", "There were undefined citations")
            for marker in failures:
                if marker in log:
                    raise ValueError(f"{stem}: {marker}")
        suffixes = (".pdf", ".aux", ".log") if args.keep_logs else (".pdf",)
        for language in ("en", "zh"):
            for extension in suffixes:
                name = f"paper-{language}{extension}"
                shutil.copyfile(work / name, args.output_dir / name)
            print(args.output_dir / f"paper-{language}.pdf")


if __name__ == "__main__":
    main()
