"""Rigorous off-edge mesh comparisons and a direct image-sum test at s=9."""

from fractions import Fraction as F
from math import ceil, comb, floor

from probe_six_site_transition import SCALE, mesh_bounds, mesh_orbits
from verify_exact_clusters import canonical, certified_energy, positions


MESH = 24
FLOORS = (F(1, 10**6), F(".07"), F(".127077875"), F(".128"),
          F(".129662031"), F(".15"), F(1, 6) - F(1, 10**8))


def mesh_comparisons():
    rows = mesh_orbits(MESH)
    edge = {canonical((0, 0, j, 0, 0, MESH-j)) for j in range(MESH//2 + 1)}
    outside = [row for row in rows if row not in edge]
    assert len(rows) == len(set(rows)) == len(outside) + len(edge)

    def orbit_size(row):
        return len({r[k:] + r[:k] for r in (row, row[::-1]) for k in range(6)})

    assert sum(map(orbit_size, rows)) == comb(MESH + 5, 5)
    print(f"M={MESH}, {len(rows)} distinct orbits, {len(outside)} outside the packed edge")
    for h in FLOORS:
        # Each interval encloses 3(E - 1 + G_9(0)), in units of 10^-24.
        bounds = mesh_bounds(MESH, h, exponent=9)
        edge_bounds = [bounds(row) for row in edge]
        edge_lo, edge_hi = map(min, zip(*edge_bounds))
        outside_bounds = [bounds(row) for row in outside]
        outside_lo, outside_hi = map(min, zip(*outside_bounds))
        gap_lo = F(outside_lo - edge_hi, 3*SCALE)
        gap_hi = F(outside_hi - edge_lo, 3*SCALE)
        assert 0 < gap_lo <= gap_hi, (h, gap_lo, gap_hi)
        possible = [r for r, (lo, _) in zip(outside, outside_bounds) if lo <= outside_hi]
        print(f"h={h}, min(off mesh)-min(edge mesh) in "
              f"[{floor(gap_lo*10**22)}, {ceil(gap_hi*10**22)}]e-22; "
              f"best off-edge candidates on mesh={possible}")


def compare_shifts():
    h = F(".128")

    def energy(t):
        sites = [0, h, 2*h, F(1, 2)+t, F(1, 2)+t+h, F(1, 2)+t+2*h]
        assert min(b-a for a, b in zip(sites, sites[1:] + [1])) >= h
        return certified_energy(sites, s=9, radius=5)

    middle = energy(F(".07"))
    for label, shift in (("center", 0), ("five contacts", F(1, 2)-3*h)):
        lo, hi = energy(shift)
        low, high = lo-middle[1], hi-middle[0]
        assert 0 < low <= high
        print(f"h={h}, E({label})-E(t=.07) in "
              f"[{floor(low*10**15)}, {ceil(high*10**15)}]e-15")


def check_off_edge_finalist():
    """Replay the h=.128 near-counterexample using only rational coordinates."""
    h = F(".128")

    def energy(units):
        gaps = [h + (1-6*h)*F(n, sum(units)) for n in units]
        assert sum(gaps) == 1 and min(gaps) >= h
        return certified_energy(positions(gaps), s=9, radius=4)

    # Three strictly slack gaps put the middle cell outside every packed edge.
    off = energy((0, 0, 214827, 0, 1, 833748))
    centered = energy((0, 0, 1, 0, 0, 1))
    shifted = energy((0, 0, 874230455480, 0, 0, 225281172296))
    for label, higher, lower, expected in (
        ("center - competitor", centered, off, (822205820553877953, 822205820553877954)),
        ("competitor - shifted", off, shifted, (718951318638981, 718951318638982)),
    ):
        bounds = (floor((higher[0]-lower[1])*10**22), ceil((higher[1]-lower[0])*10**22))
        assert bounds == expected and bounds[0] > 0
        print(f"h={h}, {label} in {bounds}e-22")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Enable Python assertions for this certificate.")
    mesh_comparisons()
    compare_shifts()
    check_off_edge_finalist()
