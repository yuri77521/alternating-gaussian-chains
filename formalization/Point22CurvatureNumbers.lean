import CertRootExp
import CertTree

/-! Closed width-22 curvature enclosures, evaluated in the Lean kernel. -/
namespace GaussianChains.Point22.Curvature
open GaussianChains.Cert GaussianChains.CertExp Set

/-- Bounds a single image at nonnegative distances in [a,b]. -/
def singleBox (a b : ℚ) : Interval :=
  Interval.mul ⟨1936*a^2-44, 1936*b^2-44⟩
    ⟨(negExpBox (22*b^2)).1, (negExpBox (22*a^2)).2⟩


/-- Encloses G'' throughout the real interval, adding both infinite tails. -/
def rawBox (a b : ℚ) : Interval :=
  (((singleBox a b).add (singleBox (1-b) (1-a))).add ⟨-1/100,1/100⟩)


def packedBox (a b : ℚ) : Interval :=
  ((rawBox (a-1/1000) (b-1/1000)).add (rawBox a b).neg).add (rawBox (a+1/1000) (b+1/1000))


inductive Test
  | near | sides | diagonals | packedSides | packedDiagonals


def check : Test → ℚ → ℚ → Bool
  | .near,a,b => decide (0 ≤ a ∧ b ≤ 1 ∧ (rawBox a b).hi < -38)
  | .sides,a,b => decide (0 ≤ a ∧ b ≤ 1 ∧ 14 < (rawBox a b).lo)
  | .diagonals,a,b => decide (0 ≤ a ∧ b ≤ 1 ∧ (rawBox a b).hi < 7)
  | .packedSides,a,b => decide (1/1000 ≤ a ∧ b ≤ 999/1000 ∧ 14 < (packedBox a b).lo)
  | .packedDiagonals,a,b => decide (1/1000 ≤ a ∧ b ≤ 999/1000 ∧ (packedBox a b).hi < 7)


def cover (k : Test) : ℕ → ℚ → ℚ → Bool
  | 0,a,b => check k a b
  | n+1,a,b => check k a b || (cover k n a ((a+b)/2) && cover k n ((a+b)/2) b)


set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem near_ok : cover .near 0 0 (4/100) = true := by decide +kernel
theorem sides_ok : cover .sides 4 (21/100) (33/100) = true := by decide +kernel
theorem diag_ok : cover .diagonals 4 (42/100) (58/100) = true := by decide +kernel
theorem pack_sides_ok : cover .packedSides 7 (21/100) (31/100) = true := by decide +kernel
theorem pack_diag_ok : cover .packedDiagonals 8 (42/100) (58/100) = true := by decide +kernel


end GaussianChains.Point22.Curvature
