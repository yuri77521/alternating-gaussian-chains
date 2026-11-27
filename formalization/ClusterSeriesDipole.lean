import ClusterSeriesExpansion
import KernelFourier

namespace GaussianChains.ClusterSeries

open Real
open scoped Asymptotics

/-- The constant term in the energy expansion, expressed using real-space
kernels as in the paper. No assertion of minimality is needed here. -/
noncomputable def dipoleEnergy (N : ℕ) (s : ℝ) : ℝ :=
  1 - 2 * (kernel s 0 - kernel s (1/2)) / N

theorem kernel_dipole_difference {s : ℝ} (hs : 0 < s) :
    kernel s 0 - kernel s (1/2) =
      4 * sqrt (π/s) * parityMoment Odd (exp (-(π^2)/s)) 0 := by
  let q := exp (-(π^2)/s)
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hs)
  let f (d : ℝ) (n : ℕ) := q^((n+1)^2) * cos (2*π*((n+1:ℕ):ℝ)*d)
  have hhalf (n : ℕ) : 2*π*((n+1:ℕ):ℝ)*(1/2) = ((n+1:ℕ):ℝ)*π := by ring
  have h : HasSum (fun n => f 0 n - f (1/2) n) (2 * parityMoment Odd q 0) := by
    apply ((parityMoment_hasSum Odd hq hq1 0).mul_left (2:ℝ)).congr_fun
    intro n
    dsimp [f]
    rw [hhalf, cos_nat_mul_pi]
    rcases Nat.even_or_odd (n+1) with he | ho
    · simp [parityTerm, he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
    · simp [parityTerm, ho.neg_one_pow, ho]
      ring
  have hf (d : ℝ) : Summable (f d) := summable_cos_modes hs d
  have hdiff : (∑' n, f 0 n) - ∑' n, f (1/2) n = 2 * parityMoment Odd q 0 := by
    rw [← (hf 0).tsum_sub (hf (1/2))]
    exact h.tsum_eq
  rw [kernel_fourier hs, kernel_fourier hs]
  change sqrt (π/s)*(1+2*(∑' n, f 0 n)) - sqrt (π/s)*(1+2*(∑' n, f (1/2) n)) =
    4 * sqrt (π/s) * parityMoment Odd q 0
  calc
    _ = 2*sqrt (π/s) * ((∑' n, f 0 n) - ∑' n, f (1/2) n) := by ring
    _ = _ := by rw [hdiff]; ring

/-- The polynomial on the right of Eq. (7) at any positive width. It applies
to the packed candidate independently of the minimizer classification. -/
noncomputable def energyPoly (k l N : ℕ) (s η : ℝ) : ℝ :=
  let A := coeff k
  let B := coeff l
  let q := exp (-(π^2)/s)
  let c := sqrt (π/s)
  dipoleEnergy N s + (4*c*(A+B)/N) * parityMoment Odd q 2 * η^2 -
    (2*c/N) * (((A+B)^2/4 + (A*(A-1)+B*(B-1))/6) * parityMoment Odd q 4 +
      ((A-B)^2/4) * parityMoment Even q 4) * η^4

theorem energyPoly_eq (k l N : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    energyPoly k l N s η = 1 - 2*sqrt (π/s)/N * massPoly k l (exp (-(π^2)/s)) η := by
  unfold energyPoly dipoleEnergy massPoly
  rw [kernel_dipole_difference hs]
  ring

theorem packedEnergy_fourth_dipole (k l N : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun η : ℝ => (1 - 2*sqrt (π/s)/N * packedMass k l (exp (-(π^2)/s)) η) -
      energyPoly k l N s η) =O[nhds 0] (fun η : ℝ => η^6) := by
  simp_rw [energyPoly_eq k l N hs]
  exact packedEnergy_fourth k l (exp_pos _) (exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hs)) _ _

#print axioms packedEnergy_fourth_dipole

end GaussianChains.ClusterSeries

