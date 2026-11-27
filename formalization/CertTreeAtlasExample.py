"""Extract the first genuine order leaf from the frozen 111111 atlas.

Only the visited rational endpoints are used as candidate data. The exclusion itself
is proved by CertTreeAtlasExample.lean, including when called without this extractor.
Run from this file's directory with Python 3.
"""
import argparse
from functools import lru_cache
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "study" / "code"))
import verify_six_site_s22_block_atlas as atlas


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="refresh just the box declaration")
    write = parser.parse_args().write
    nodes = atlas.gaussian_nodes()
    kernel = lru_cache(None)(lambda a, b: atlas.BlockKernel(nodes, a, b))
    floor = atlas.signed_point_score(nodes, [v * atlas.H for v in atlas.WITNESS])
    # Stop after recording the first order terminal without changing the verifier.
    class FirstOrder(Exception):
        pass

    # Line events precede execution of the line. Only this function's frame is traced.
    lines = Path(atlas.__file__).read_text(encoding="utf-8").splitlines()
    order_line, = [i for i, line in enumerate(lines, 1) if 'stats["order"] += 1' in line]

    def capture(frame, event, arg):
        if frame.f_code is atlas.verify_face.__code__:
            if event == "line" and frame.f_lineno == order_line:
                state = frame.f_locals
                print("grid", atlas.GRID, "word", state["word"])
                print("lo", state["lo"], "hi", state["hi"])
                print("visited", state["stats"]["visited"])
                lower, upper = state["lo"], state["hi"]
                def q(v):
                    return "0" if not v else f"{v}/{atlas.GRID}"
                entries = [f"⟨{q(a)},{q(b)}⟩" for a, b in zip(lower, upper)]
                declaration = ("def box : Box 6 :=\n  ![" + ", ".join(entries[:3])
                               + ",\n    " + ", ".join(entries[3:]) + "]")
                path = Path(__file__).with_name("CertTreeAtlasExample.lean")
                source = path.read_text(encoding="utf-8")
                start = source.index("def box : Box 6 :=")
                end = source.index("\n\n", start)
                if write:
                    path.write_text(source[:start] + declaration + source[end:], encoding="utf-8")
                elif declaration != source[start:end]:
                    raise RuntimeError("Frozen atlas differs; rerun with --write to refresh the proof data")
                raise FirstOrder
            return capture
        return None

    try:
        sys.settrace(capture)
        atlas.verify_face((1,) * 6, nodes, kernel, floor)
    except FirstOrder:
        return
    finally:
        sys.settrace(None)
    raise RuntimeError("No order terminal reached")


if __name__ == "__main__":
    main()
