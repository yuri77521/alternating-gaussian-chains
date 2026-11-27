import ClusterSeriesAmplitude
import ChainFourier

/-! Substitution of the antipodal packed configuration in the general
ordered-pair Gaussian energy. These identities require no minimizing hypothesis. -/
noncomputable section

namespace GaussianChains.ClusterSeries

/-- Positions on the unit-period circle of the two packed blocks, in the lift
whose first midpoint is zero. The argument `h` is the period-normalized gap. -/
def packedSites (k l : ℕ) (h : ℝ) (j : Fin ((2*k+1)+(2*l+1))) : ℝ :=
  packedAngle k l (2*Real.pi*h) j.val / (2*Real.pi)

theorem structureFactor_packed (k l n : ℕ) (h : ℝ) :
    structureFactor (packedSites k l h) n =
      ((block k (n*(2*Real.pi*h)) -
        (-1 : ℝ)^n * block l (n*(2*Real.pi*h)) : ℝ) : ℂ) := by
  rw [← packed_pair_sum]
  unfold structureFactor
  apply Finset.sum_congr rfl
  intro j _
  have ha : 2*Real.pi*(n:ℝ)*packedSites k l h j =
      n*packedAngle k l (2*Real.pi*h) j.val := by
    unfold packedSites
    field_simp [Real.pi_ne_zero]
  simp [ha, phase, charge]

theorem norm_structureFactor_packed_sq (k l n : ℕ) (h : ℝ) :
    ‖structureFactor (packedSites k l h) n‖ ^ 2 =
      (block k (n*(2*Real.pi*h)) - (-1:ℝ)^n * block l (n*(2*Real.pi*h)))^2 := by
  rw [structureFactor_packed, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Equation (6) for the candidate configurations, including unequal odd block
lengths and their even modes, at every positive Gaussian width. -/
theorem imageEnergy_packedSites (k l : ℕ) {s : ℝ} (hs : 0 < s) (h : ℝ) :
    imageEnergy s (packedSites k l h) =
      1 - 2 * Real.sqrt (Real.pi/s)/(((2*k+1)+(2*l+1) : ℕ):ℝ) *
        packedMass k l (Real.exp (-(Real.pi^2)/s)) (2*Real.pi*h) := by
  have hf {N : ℕ} (hN : ∃ m, N=2*m) (x : Fin N → ℝ) :
      imageEnergy s x = 1 - 2*Real.sqrt (Real.pi/s)/(N:ℝ) *
        ∑' r : ℕ, Real.exp (-(Real.pi^2)/s)^((r+1)^2) * ‖structureFactor x (r+1)‖^2 := by
    obtain ⟨m,rfl⟩ := hN
    exact imageEnergy_fourier m hs x
  rw [hf (N := (2*k+1)+(2*l+1)) ⟨k+l+1, by omega⟩, packedMass]
  simp only [norm_structureFactor_packed_sq]

/-- Interchanging which odd block starts with a positive charge preserves
the energy, even when the two labeled configurations occupy different orbits. -/
theorem packedMass_swap (k l : ℕ) (q η : ℝ) :
    packedMass k l q η = packedMass l k q η := by
  apply tsum_congr
  intro n
  rcases Nat.even_or_odd (n+1) with he | ho
  · rw [he.neg_one_pow]
    ring
  · rw [ho.neg_one_pow]
    ring

theorem imageEnergy_swap_blocks (k l : ℕ) {s : ℝ} (hs : 0 < s) (h : ℝ) :
    imageEnergy s (packedSites k l h) = imageEnergy s (packedSites l k h) := by
  rw [imageEnergy_packedSites k l hs, imageEnergy_packedSites l k hs,
    packedMass_swap k l, Nat.add_comm (2*k+1) (2*l+1)]

/-- Physical-lift form of the same identity at arbitrary positive period L. -/
theorem physicalEnergy_packedSites (k l : ℕ) {α L : ℝ} (hα : 0 < α)
    (hL : 0 < L) (h : ℝ) :
    physicalEnergy α L (fun j => L * packedSites k l h j) =
      1 - 2 * Real.sqrt (Real.pi/(α*L^2))/(((2*k+1)+(2*l+1) : ℕ):ℝ) *
        packedMass k l (Real.exp (-(Real.pi^2)/(α*L^2))) (2*Real.pi*h) := by
  rw [physicalEnergy_eq_imageEnergy (N := (2*k+1)+(2*l+1)) (by omega) α L hα hL]
  simpa [hL.ne'] using imageEnergy_packedSites k l (s := α*L^2) (by positivity) h

#print axioms structureFactor_packed
#print axioms imageEnergy_packedSites
#print axioms physicalEnergy_packedSites

end GaussianChains.ClusterSeries
