"""Regenerate the candidate nome and scale endpoints checked in CertTreeWidthSamples.lean.

Run without arguments to print the seven Lean declarations, or pass --check to
compare them with the source. The mathematical checks are the w*_valid proofs.
"""
from argparse import ArgumentParser
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from pathlib import Path


WIDTHS = [
    ("799", "7.99", "(799/100)"),
    ("800", "8", "8"),
    ("801", "8.01", "(801/100)"),
    ("825", "8.25", "(33/4)"),
    ("850", "8.5", "(17/2)"),
    ("875", "8.75", "(35/4)"),
    ("900", "9", "9"),
]


def declarations():
    with localcontext() as context:
        context.prec = 64
        pi = Decimal("3.14159265358979323846264338327950288419716939937510")
        grid = Decimal(10) ** 16
        for label, decimal, lean in WIDTHS:
            s = Decimal(decimal)
            q = (-(pi**2) / s).exp()
            c = (pi / s).sqrt()
            lower = int((grid * q).to_integral_value(rounding=ROUND_FLOOR))
            upper = lower + 1
            scale = int((grid * c).to_integral_value(rounding=ROUND_CEILING))
            yield f"def w{label} := sample {lean} {lower} {upper} {scale}"


if __name__ == "__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--check", action="store_true")
    args = cli.parse_args()
    generated = list(declarations())
    if args.check:
        source = Path(__file__).with_suffix(".lean").read_text(encoding="utf-8")
        stored = [line for line in source.splitlines() if line.startswith("def w") and ":= sample " in line]
        if generated != stored:
            raise SystemExit("Generated width samples differ from the Lean input.")
        print(f"Matched {len(generated)} candidate width samples.")
    else:
        print("\n".join(generated))
