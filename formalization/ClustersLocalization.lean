import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative semicircle localization. Angles are in radians.
A radius in a quadrant is measured from the nearest jump of the reference semicircle. -/
noncomputable section

namespace GaussianChains.Localization

open Real MeasureTheory Set Finset

/-- Among densities bounded by one, putting all their mass next to zero
minimizes the first radial moment. -/
theorem quadrant_mass_moment {T : ℝ} (hT : 0 ≤ T) {d : ℝ → ℝ}
    (hi : IntervalIntegrable d volume 0 T)
    (hr : ∀ t ∈ Icc 0 T, 0 ≤ d t ∧ d t ≤ 1) :
    (∫ t in 0..T, d t)^2 ≤ 2 * ∫ t in 0..T, t * d t := by
  let a := ∫ t in 0..T, d t
  have h0 : 0 ≤ a := intervalIntegral.integral_nonneg hT fun t ht => (hr t ht).1
  have h1 : a ≤ T := by
    have h := intervalIntegral.integral_mono_on hT hi (intervalIntegrable_const (c := (1:ℝ)))
      (fun t ht => (hr t ht).2)
    simpa [a] using h
  have hiL : IntervalIntegrable d volume 0 a :=
    hi.mono_set (by simpa [uIcc_of_le hT, uIcc_of_le h0] using Icc_subset_Icc le_rfl h1)
  have hiR : IntervalIntegrable d volume a T :=
    hi.mono_set (by simpa [uIcc_of_le hT, uIcc_of_le h1] using Icc_subset_Icc h0 le_rfl)
  have lin : IntervalIntegrable (fun t => t * d t) volume 0 a :=
    hiL.continuousOn_mul continuous_id.continuousOn
  have rin : IntervalIntegrable (fun t => t * d t) volume a T :=
    hiR.continuousOn_mul continuous_id.continuousOn
  have hleft := intervalIntegral.integral_mono_on h0
    ((continuous_id.sub continuous_const).intervalIntegrable 0 a)
    (lin.sub (hiL.const_mul a))
    (f := fun t => t - a) (g := fun t => t*d t - a*d t) (by
      intro t ht
      have hd := (hr t ⟨ht.1, ht.2.trans h1⟩).2
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hd)])
  have hright := intervalIntegral.integral_mono_on h1 (hiR.const_mul a) rin
    (f := fun t => a*d t) (g := fun t => t*d t) (by
      intro t ht
      exact mul_le_mul_of_nonneg_right ht.1 (hr t ⟨h0.trans ht.1, ht.2⟩).1)
  dsimp only at hleft hright
  rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => a) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, intervalIntegral.integral_sub lin
        (hiL.const_mul a), intervalIntegral.integral_const_mul] at hleft
  rw [intervalIntegral.integral_const_mul] at hright
  rw [← intervalIntegral.integral_add_adjacent_intervals lin rin]
  have had : (∫ t in 0..a, d t) + (∫ t in a..T, d t) = a :=
    intervalIntegral.integral_add_adjacent_intervals hiL hiR
  change a^2 ≤ _
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), smul_eq_mul] at hleft
  nlinarith only [hleft, hright, congrArg (a * ·) had]

/-- The sine-weighted mass controls the mass squared on a quadrant. -/
theorem quadrant_mass_sine {d : ℝ → ℝ}
    (hi : IntervalIntegrable d volume 0 (π/2))
    (hr : ∀ t ∈ Icc 0 (π/2), 0 ≤ d t ∧ d t ≤ 1) :
    (∫ t in 0..π/2, d t)^2 ≤ π * ∫ t in 0..π/2, sin t * d t := by
  have hT : 0 ≤ π/2 := by positivity
  have h := quadrant_mass_moment hT hi hr
  have hi' : IntervalIntegrable (fun t => t * d t) volume 0 (π/2) :=
    hi.continuousOn_mul continuous_id.continuousOn
  have hk := intervalIntegral.integral_mono_on hT (hi'.const_mul (2/π))
    (hi.continuousOn_mul continuous_sin.continuousOn)
    (f := fun t => 2/π * (t*d t)) (g := fun t => sin t*d t) (by
      intro t ht
      dsimp only
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_sin ht.1 ht.2) (hr t ht).1)
  dsimp only at hk
  rw [intervalIntegral.integral_const_mul] at hk
  have hh := mul_le_mul_of_nonneg_left hk pi_pos.le
  field_simp [ne_of_gt pi_pos] at hh
  linarith

/-- Partition the symmetric difference with a semicircle at both endpoints
and both midpoints. Each of the four resulting densities is parametrized
by its distance to the nearer endpoint. -/
theorem discrepancy_mass_sq_le (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hr : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1) :
    (∑ i, ∫ t in 0..π/2, d i t)^2 ≤
      4 * π * ∑ i, ∫ t in 0..π/2, sin t * d i t := by
  let b := fun i => ∫ t in 0..π/2, d i t
  have hh (i : Fin 4) := quadrant_mass_sine (hi i) (hr i)
  have hs := Finset.sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ => hh i
  rw [← Finset.mul_sum] at hs
  have hvar : (∑ i, b i)^2 ≤ 4 * ∑ i, (b i)^2 := by
    simp only [Fin.sum_univ_four]
    nlinarith only [sq_nonneg (b 0-b 1),sq_nonneg (b 0-b 2),sq_nonneg (b 0-b 3),
      sq_nonneg (b 1-b 2),sq_nonneg (b 1-b 3),sq_nonneg (b 2-b 3)]
  change (∑ i, b i)^2 ≤ _
  exact hvar.trans (by dsimp [b]; linarith only [hs])

/-- For an even harmonic the semicircle mode vanishes. The two elementary
bounds are obtained by integrating the signed difference, and by subtracting
one half from the arc indicator over a full turn. -/
theorem even_mode_bound {n z b P : ℝ} (hn : 2 ≤ n) (hz : 0 ≤ z) (hz' : z ≤ 2)
    (hb : b^2 ≤ 4*π*(2-z)) (hm : P ≤ n^2*b^2) (hu : P ≤ n^2*π^2) :
    P ≤ n^4*(4-z^2) := by
  have hn2 : 4 ≤ n^2 := by nlinarith [sq_nonneg (n-2)]
  by_cases hs : z ≤ 6/5
  · have hπ : π^2 ≤ (3.15:ℝ)^2 := pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2
    have hzz : z^2 ≤ (6/5:ℝ)^2 := pow_le_pow_left₀ hz hs 2
    have hw : π^2 ≤ n^2*(4-z^2) := by
      nlinarith only [hπ, hzz, hn2, mul_nonneg (sub_nonneg.mpr hn2)
        (show 0 ≤ 4-z^2 by linarith only [hzz])]
    calc P ≤ _ := hu
         _ ≤ n^2 * (n^2*(4-z^2)) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
         _ = _ := by ring
  · have hc : 4*π ≤ n^2*(2+z) := by
      nlinarith only [pi_lt_d2, not_le.mp hs,
        mul_nonneg (sub_nonneg.mpr hn2) (show 0 ≤ 2+z by linarith only [hz])]
    have hc' := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hz')
    calc P ≤ _ := hm
         _ ≤ n^2*(4*π*(2-z)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
         _ ≤ n^2*(n^2*(2+z)*(2-z)) := mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
         _ = _ := by ring

/-- In an odd harmonic of order at least three the linear error of the
squared amplitude is bounded by four times the sine-weighted discrepancy. -/
theorem odd_mode_bound {n z b P : ℝ} (hn : 3 ≤ n) (hz : 0 ≤ z) (hz' : z ≤ 2)
    (hb : b^2 ≤ 4*π*(2-z)) (hm : P-4 ≤ n^2*(4*(2-z)+b^2)) :
    P-4 ≤ n^4*(4-z^2) := by
  have hn2 : 9 ≤ n^2 := by nlinarith [sq_nonneg (n-3)]
  have hc : 4+4*π ≤ n^2*(2+z) := by
    nlinarith only [pi_lt_d2, hn2, mul_nonneg (sq_nonneg n) hz]
  have hc' := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hz')
  calc P-4 ≤ _ := hm
       _ ≤ n^2*((4+4*π)*(2-z)) := mul_le_mul_of_nonneg_left (by linarith only [hb]) (sq_nonneg _)
       _ ≤ n^2*(n^2*(2+z)*(2-z)) := mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
       _ = _ := by ring

/-- Sum the higher-mode losses relative to the semicircle. The first
mode is kept separate, as in equation (3). Here w is its normalized tail
and loss is the difference of squared amplitudes, configuration minus dipole. -/
theorem semicircle_deficit_of_mode_bounds {w loss : ℕ → ℝ} {z : ℝ}
    (hz : 0 ≤ z) (hz' : z ≤ 2) (hw0 : ∀ k, 0 ≤ w k)
    (hw : Summable fun k => w k * ((k+2:ℕ):ℝ)^4)
    (hl : Summable fun k => w k * loss k)
    (hR : ∑' k, w k * ((k+2:ℕ):ℝ)^4 ≤ 2/3)
    (hmode : ∀ k, loss k ≤ ((k+2:ℕ):ℝ)^4 * (4-z^2)) :
    (4-z^2)/3 ≤ 4-z^2 - ∑' k, w k * loss k := by
  have htail := hl.tsum_le_tsum (g := fun k => (w k * ((k+2:ℕ):ℝ)^4) * (4-z^2))
    (fun k => by dsimp only; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hmode k) (hw0 k))
    (hw.mul_right _)
  rw [tsum_mul_right] at htail
  have hgap : 0 ≤ 4-z^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hz') (show 0 ≤ 2+z by linarith)]
  linarith only [htail, mul_le_mul_of_nonneg_right hR hgap]

/-- Convert the semicircle deficit and the trial-state energy upper bound to
the discrepancy bound used for the hard spacing argument. -/
theorem discrepancy_of_trial {z F m η : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 2)
    (hF : (4-z^2)/3 ≤ F) (hut : F ≤ 2*m^2*η^2) :
    2-z ≤ 3*m^2*η^2 := by
  nlinarith only [mul_nonneg hz (sub_nonneg.mpr hz'), hF, hut]

/-- A jump farther than one floor unit from the semicircle boundary must
have an adjacent discrepant half-gap. Its integral cost gives the explicit
constant C = 1 + 3πm² from the published localization argument. -/
theorem endpoint_radius_of_discrepant_gap {J m η r : ℝ} (hη : 0 < η)
    (hu : J ≤ 3*m^2*η^2) (hc : η ≤ r → η/π*(r-η/2) ≤ J) :
    r ≤ (1+3*π*m^2)*η := by
  by_cases hr : η ≤ r
  · have ht := mul_le_mul_of_nonneg_left ((hc hr).trans hu) pi_pos.le
    field_simp [ne_of_gt pi_pos] at ht
    linarith only [ht, hη]
  · exact (not_le.mp hr).le.trans (by nlinarith [mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg m)) hη.le])

end GaussianChains.Localization

