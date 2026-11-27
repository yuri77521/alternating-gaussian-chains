import ChainFourier
import PackedFaceClassification
import PackedFaceModes
import PackedFaceSeries

/-! The packed-face energy is the physical unit-period image energy, reduced
to one real Chebyshev coordinate by the absolutely convergent Fourier series. -/

noncomputable section
namespace GaussianChains.PackedFace

theorem structureFactor_sites_sq (n : ℕ) (h t : ℝ) :
    ‖structureFactor (sites h t) n‖^2 =
      2 * amplitude h n ^ 2 *
        (1 - (-1 : ℝ)^n * Real.cos (2 * Real.pi * n * t)) := by
  have hexp : structureFactor (sites h t) n =
      wave n 0 - wave n h + wave n (2*h) - wave n (1/2+t) +
        wave n (1/2+t+h) - wave n (1/2+t+2*h) := by
    change (∑ j : Fin 6, (charge j : ℂ) * wave n (sites h t j)) = _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [sites, Matrix.cons_val_succ, Matrix.cons_val_zero]
    norm_num [charge, Matrix.cons_val]
    <;> ring
  rw [hexp, norm_six_wave_sq, amplitude, Polynomial.Chebyshev.T_real_cos]
  push_cast
  ring_nf

/-- Difference of modal powers at the centered and translated cells. -/
theorem centered_power_sub (q h t : ℝ) (k : ℕ) :
    q^((k+1)^2) * ‖structureFactor (sites h 0) (k+1)‖^2 -
        q^((k+1)^2) * ‖structureFactor (sites h t) (k+1)‖^2 =
      (2*q) * phiMode q h (coord t) (k+1) := by
  rw [structureFactor_sites_sq, structureFactor_sites_sq]
  simp only [mul_zero, Real.cos_zero, mul_one]
  unfold phiMode coord
  rw [sub_sub_cancel, Polynomial.Chebyshev.T_real_cos]
  have hpos : 1 ≤ (k+1)^2 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
  have he : q^((k+1)^2) = q^((k+1)^2-1)*q := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [he]
  push_cast
  ring_nf

/-- Equation (9) with the original image energy at each of its two cells.
The reduction holds for every positive width and every real displacement. -/
theorem imageEnergy_difference {s : ℝ} (hs : 0 < s) (h t : ℝ) :
    imageEnergy s (sites h t) - imageEnergy s (sites h 0) =
      (4 * Real.sqrt (Real.pi/s) * Real.exp (-(Real.pi^2)/s) / 6) *
        phi (Real.exp (-(Real.pi^2)/s)) h (coord t) := by
  let q := Real.exp (-(Real.pi^2)/s)
  let w (t : ℝ) (k : ℕ) := q^((k+1)^2) * ‖structureFactor (sites h t) (k+1)‖^2
  have hw (t : ℝ) : Summable (w t) := fourier_summable _ hs
  have hsum : (∑' k, w 0 k) - (∑' k, w t k) = (2*q) * phi q h (coord t) := by
    rw [← (hw 0).tsum_sub (hw t)]
    unfold phi
    rw [← tsum_mul_left]
    exact tsum_congr (centered_power_sub q h t)
  rw [imageEnergy_fourier 3 hs (sites h t), imageEnergy_fourier 3 hs (sites h 0)]
  change (1 - 2 * Real.sqrt (Real.pi/s) / 6 * ∑' k, w t k) -
      (1 - 2 * Real.sqrt (Real.pi/s) / 6 * ∑' k, w 0 k) =
    4 * Real.sqrt (Real.pi/s) * q / 6 * phi q h (coord t)
  linear_combination (2 * Real.sqrt (Real.pi/s) / 6) * hsum

/-- At positive width the scalar multiplying the Chebyshev score is positive,
so the order of the *physical* energies agrees exactly with its order. -/
theorem imageEnergy_le_iff {s : ℝ} (hs : 0 < s) (h t u : ℝ) :
    imageEnergy s (sites h t) ≤ imageEnergy s (sites h u) ↔
      phi (Real.exp (-(Real.pi^2)/s)) h (coord t) ≤
        phi (Real.exp (-(Real.pi^2)/s)) h (coord u) := by
  rw [← sub_le_sub_iff_right (imageEnergy s (sites h 0)),
    imageEnergy_difference hs h t, imageEnergy_difference hs h u]
  exact mul_le_mul_iff_right₀ (by positivity)

/-- The full constrained minimum problem on the closed packed face is
equivalent to minimizing the real scalar score on its entire closed interval. -/
theorem minimizes_iff_phi {s h t : ℝ} (hs : 0 < s) (hh : 0 ≤ h) (hh' : h ≤ 1/6)
    (ht : feasible h t) :
    Minimizes (fun u => imageEnergy s (sites h u)) {u | feasible h u} t ↔
      Minimizes (phi (Real.exp (-(Real.pi^2)/s)) h)
        (Set.Icc 0 (coord (bound h))) (coord t) := by
  rw [← minimizes_comp_coord_iff _ hh hh' ht]
  constructor
  · intro H
    exact ⟨H.1, fun u hu => (imageEnergy_le_iff hs h t u).mp (H.2 u hu)⟩
  · intro H
    exact ⟨H.1, fun u hu => (imageEnergy_le_iff hs h t u).mpr (H.2 u hu)⟩

end GaussianChains.PackedFace
