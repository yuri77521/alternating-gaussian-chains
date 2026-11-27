import ClusterSeriesDefs
import Mathlib.Tactic.Ring

/-! Fourier amplitudes of antipodal packed progressions, using angular coordinates. -/
noncomputable section

namespace GaussianChains.ClusterSeries

open scoped BigOperators

/-- Complex phase at angle `u`. -/
def phase (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * Complex.I)

private theorem phase_add (u v : ℝ) : phase (u+v) = phase u * phase v := by
  simp [phase, add_mul, Complex.exp_add]

private theorem phase_pair (u : ℝ) :
    phase (-u) + phase u = 2 * (Real.cos u : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [phase, Complex.ofReal_neg]
  ring

private theorem phase_pi (n : ℕ) : phase ((n : ℝ)*Real.pi) = (-1 : ℂ)^n := by
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- Label zero has charge +1. Its angular offset from the midpoint is `-k*w`. -/
def siteTerm (k : ℕ) (w : ℝ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * phase (((j : ℝ) - k)*w)

private theorem term_shift (k i : ℕ) (w : ℝ) :
    siteTerm (k+1) w (i+1) = -siteTerm k w i := by
  unfold siteTerm
  push_cast
  rw [pow_succ, show (i : ℝ)+1-(k+1) = i-k by ring]
  ring

/-- The recursive real cosine amplitude is exactly the complex Fourier sum
of all the particles, including both endpoints of the odd block. -/
theorem packed_sum (k : ℕ) (w : ℝ) :
    ∑ j ∈ Finset.range (2*k+1), siteTerm k w j = (block k w : ℂ) := by
  induction k with
  | zero => simp [siteTerm, phase, block]
  | succ k ih =>
    let f := siteTerm (k+1) w
    change ∑ j ∈ Finset.range (2*(k+1)+1), f j = _
    rw [show 2*(k+1)+1 = ((2*k+1)+1)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ' f (2*k+1)]
    have hs : ∑ j ∈ Finset.range (2*k+1), f (j+1) = -(block k w : ℂ) := by
      simp only [f, term_shift, Finset.sum_neg_distrib, ih]
    rw [hs]
    have hZ : f 0 = phase (-(((k:ℝ)+1)*w)) := by
      simp [f, siteTerm]
      congr 1
      ring
    have hL : f ((2*k+1)+1) = phase (((k:ℝ)+1)*w) := by
      unfold f siteTerm
      rw [show (2*k+1)+1 = 2*(k+1) by omega, pow_mul]
      push_cast
      simp only [neg_one_sq, one_pow, one_mul]
      congr 2
      ring
    rw [hZ, hL, block]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    linear_combination phase_pair (((k:ℝ)+1)*w)

/-- Angular coordinates of the two packed progressions before an arbitrary
common rotation. The second midpoint lies at angle π and its first sign is −. -/
def packedAngle (k l : ℕ) (η : ℝ) (j : ℕ) : ℝ :=
  if j < 2*k+1 then ((j : ℝ)-k)*η
  else Real.pi + (((j-(2*k+1) : ℕ) : ℝ)-l)*η

/-- Complete complex amplitude over the consecutive alternating particle labels. -/
theorem packed_pair_sum (k l n : ℕ) (η : ℝ) :
    (∑ j : Fin ((2*k+1)+(2*l+1)),
      (-1 : ℂ)^j.val * phase ((n : ℝ) * packedAngle k l η j.val)) =
    ((block k (n*η) - (-1 : ℝ)^n * block l (n*η) : ℝ) : ℂ) := by
  let f (j : ℕ) := (-1 : ℂ)^j * phase ((n:ℝ)*packedAngle k l η j)
  change (∑ j : Fin ((2*k+1)+(2*l+1)), f j.val) = _
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_add]
  have hleft : ∑ j ∈ Finset.range (2*k+1), f j = (block k (n*η) : ℂ) := by
    rw [← packed_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [f, packedAngle, if_pos (Finset.mem_range.mp hj), siteTerm]
    congr 2
    ring
  have hright (j : ℕ) : f ((2*k+1)+j) =
      -((-1 : ℂ)^n * siteTerm l (n*η) j) := by
    simp only [f, packedAngle, if_neg (by omega : ¬(2*k+1)+j < 2*k+1),
      Nat.add_sub_cancel_left, pow_add, pow_succ, pow_mul,
      siteTerm, mul_add, phase_add, phase_pi]
    rw [show (n : ℝ)*(((j:ℝ)-l)*η) = ((j:ℝ)-l)*(n*η) by ring]
    ring
  rw [hleft]
  simp_rw [hright]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, packed_sum]
  push_cast
  ring

/-- Squaring the norm retains the even-frequency term when the block lengths differ. -/
theorem packed_pair_norm_sq (k l n : ℕ) (η : ℝ) :
    ‖∑ j : Fin ((2*k+1)+(2*l+1)),
      (-1 : ℂ)^j.val * phase ((n : ℝ) * packedAngle k l η j.val)‖^2 =
    (block k (n*η) - (-1 : ℝ)^n * block l (n*η))^2 := by
  rw [packed_pair_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end GaussianChains.ClusterSeries
