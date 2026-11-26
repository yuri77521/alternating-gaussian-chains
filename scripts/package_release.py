"""Build the original v1.0.1 ZIP from its exact file inventory."""
import argparse
import hashlib
from pathlib import Path
import tempfile
import zipfile

STUDY = Path(__file__).resolve().parents[1] / "study"
ZIP_SHA256 = "4fecd3792e47752374062e5340bd06f2f1ed59d25c2132df7c8df97243bcfc86"


def build(output):
    names = (STUDY / "FILES.txt").read_text("utf-8").splitlines()
    hashes = dict(line.split("  ", 1)[::-1] for line in
                  (STUDY / "SHA256SUMS.txt").read_text("utf-8").splitlines())
    if names != sorted(set(hashes) | {"SHA256SUMS.txt"}):
        raise ValueError("Unexpected frozen inventory")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as temp:
        stage = Path(temp) / "study.zip"
        with zipfile.ZipFile(stage, "w") as archive:
            for name in names:
                data = (STUDY / name).read_bytes()
                if name in hashes and hashlib.sha256(data).hexdigest() != hashes[name]:
                    raise ValueError(f"Changed frozen file: {name}")
                member = zipfile.ZipInfo(name, (2026, 11, 26, 0, 0, 0))
                member.create_system = 3
                member.external_attr = 0o100644 << 16
                archive.writestr(member, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
        if hashlib.sha256(stage.read_bytes()).hexdigest() != ZIP_SHA256:
            raise ValueError("ZIP differs from the frozen artifact")
        # Exclusive creation also protects existing releases on POSIX.
        with stage.open("rb") as src, output.open("xb") as dst:
            dst.write(src.read())
    print(f"{ZIP_SHA256}  {output.name}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    build(parser.parse_args().output)
