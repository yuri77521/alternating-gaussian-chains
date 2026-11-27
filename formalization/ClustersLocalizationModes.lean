import ClustersLocalization
import ClustersLocalizationDefs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FinCases

/-! Fourier moments in the four radial charts touching the endpoints of a
semicircle. The chart angles in order are t, π−t, π+t, 2π−t. The sign of the
discrepancy is negative in the first two quadrants and positive in the others.

Write b for the discrepancy mass and J for its sine-weighted mass. The change
of an even mode is bounded both by nb and by nπ. For an odd mode the reference
amplitude is 2i, so its squared-norm excess depends linearly only on the
imaginary part of the change. The bound |sin(nt)| ≤ n|sin t| gives the linear
error 4n²J; the quadratic error is at most n²b². With b² ≤ 4πJ these estimates
reserve one third of the first mode under the published fourth-moment condition. -/
noncomputable section

namespace GaussianChains.Localization
open Real MeasureTheory Set Finset

private theorem osc_norm (n : ℕ) (t : ℝ) : ‖osc n t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem osc_im (n : ℕ) (t : ℝ) : (osc n t).im = sin (n*t) := Complex.exp_ofReal_mul_I_im _

private theorem chartWave_norm (n : ℕ) (i : Fin 4) (t : ℝ) : ‖chartWave n i t‖ = 1 := by
  fin_cases i <;> simp [chartWave, norm_pow, osc_norm]

private theorem chartWave_continuous (n : ℕ) (i : Fin 4) : Continuous (chartWave n i) := by
  fin_cases i <;> unfold chartWave osc <;> fun_prop

private theorem sin_mul_bound (n : ℕ) (t : ℝ) : |sin (n*t)| ≤ n*|sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc _ ≤ |sin (n*t) * cos t| + |cos (n*t) * sin t| := abs_add_le _ _
         _ ≤ |sin (n*t)| * 1 + 1*|sin t| := by
             simp only [abs_mul]
             exact add_le_add
               (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _))
               (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (abs_nonneg _))
         _ ≤ _ := by linarith

private theorem chartWave_im (n : ℕ) (i : Fin 4) (t : ℝ) :
    |(chartWave n i t).im| ≤ n*|sin t| := by
  rcases neg_one_pow_eq_or ℂ n with h | h <;> fin_cases i <;>
    simpa [chartWave, h, osc_im] using sin_mul_bound n t

private theorem chartWave_sum_even (n : ℕ) (he : Even n) (t : ℝ) :
    ∑ i, chartWave n i t = 0 := by
  rw [Fin.sum_univ_four]
  simp [chartWave, he.neg_one_pow]

theorem modeChange_norm (n : ℕ) (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t) :
    ‖modeChange n d‖ ≤ n * arcMass d := by
  have hT : 0 ≤ π/2 := by positivity
  rw [modeChange, norm_smul, Real.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ n.cast_nonneg
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply intervalIntegral.norm_integral_le_of_norm_le hT _ (hi i)
  filter_upwards with t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i t (Ioc_subset_Icc_self ht)),
    chartWave_norm, mul_one]

private theorem osc_integrable (n : ℕ) (d : ℝ → ℝ) (i : Fin 4)
    (hi : IntervalIntegrable d volume 0 (π/2)) :
    IntervalIntegrable (fun t => d t • chartWave n i t) volume 0 (π/2) := by
  have hi' : IntervalIntegrable (fun t => (d t : ℂ)) volume 0 (π/2) :=
    ⟨hi.1.ofReal, hi.2.ofReal⟩
  simpa [Complex.real_smul] using hi'.mul_continuousOn (chartWave_continuous n i).continuousOn

theorem modeChange_im_le (n : ℕ) (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t) :
    (modeChange n d).im ≤ (n:ℝ)^2 * arcCost d := by
  have hT : 0 ≤ π/2 := by positivity
  have h (i : Fin 4) :
      (∫ t in 0..π/2, d i t • chartWave n i t).im ≤
        n * ∫ t in 0..π/2, sin t*d i t := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (osc_integrable n (d i) i (hi i))]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT
      ⟨(osc_integrable n (d i) i (hi i)).1.im, (osc_integrable n (d i) i (hi i)).2.im⟩
      (((hi i).continuousOn_mul continuous_sin.continuousOn).const_mul _)
    intro t ht
    change (((d i t : ℝ) : ℂ) * chartWave n i t).im ≤ (n : ℝ) * (sin t * d i t)
    rw [Complex.im_ofReal_mul]
    have hb := (le_abs_self _).trans (chartWave_im n i t)
    rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos]))] at hb
    calc d i t * _ ≤ d i t * (n*sin t) := mul_le_mul_of_nonneg_left hb (hd i t ht)
         _ = _ := by ring
  have H := Finset.sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ => h i
  rw [← Finset.mul_sum] at H
  change Complex.imCLM ((n : ℝ) • _) ≤ _
  rw [map_smul, map_sum, smul_eq_mul]
  calc _ ≤ (n:ℝ) * (n * arcCost d) := mul_le_mul_of_nonneg_left H n.cast_nonneg
       _ = _ := by ring

/-- In an even mode the four signed waves cancel pointwise. This permits
centering every discrepancy density at 1/2 before applying the triangle inequality. -/
theorem modeChange_norm_even (n : ℕ) (he : Even n) (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1) :
    ‖modeChange n d‖ ≤ n * π := by
  have hT : 0 ≤ π/2 := by positivity
  let c : ℝ := 1/2
  have hconst (i : Fin 4) :
      IntervalIntegrable (fun t => c • chartWave n i t) volume 0 (π/2) :=
    (continuous_const.smul (chartWave_continuous n i)).intervalIntegrable _ _
  have hcancel : ∑ i, (∫ t in 0..π/2, c • chartWave n i t) = 0 := by
    rw [← intervalIntegral.integral_finset_sum (fun i _ => hconst i)]
    simp only [← Finset.smul_sum, chartWave_sum_even n he, smul_zero, intervalIntegral.integral_zero]
  have hid (i : Fin 4) :
      (∫ t in 0..π/2, (d i t - c) • chartWave n i t) =
      (∫ t in 0..π/2, d i t • chartWave n i t) -
      ∫ t in 0..π/2, c • chartWave n i t := by
    simp_rw [sub_smul]
    exact intervalIntegral.integral_sub (osc_integrable n (d i) i (hi i)) (hconst i)
  have hint (i : Fin 4) : ‖∫ t in 0..π/2, (d i t - c) • chartWave n i t‖ ≤ π/4 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => (d i t - c) • chartWave n i t) (a := 0) (b := π/2) (C := c) (by
        intro t ht
        rw [uIoc_of_le hT] at ht
        obtain ⟨h0,h1⟩ := hd i t (Ioc_subset_Icc_self ht)
        rw [norm_smul, Real.norm_eq_abs, chartWave_norm, mul_one, abs_le]
        dsimp [c]
        constructor <;> linarith)
    rw [sub_zero, abs_of_nonneg hT] at h
    exact h.trans_eq (by dsimp [c]; ring)
  simp only [modeChange, norm_smul, Real.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ n.cast_nonneg
  have H := congrArg (fun a : ℂ => ‖a‖)
    (show (∑ i, (∫ t in 0..π/2, (d i t - c) • chartWave n i t)) =
       ∑ i, (∫ t in 0..π/2, d i t • chartWave n i t) by
      simp_rw [hid]; rw [sum_sub_distrib, hcancel, sub_zero])
  dsimp only at H
  rw [← H]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hint i).trans ?_)
  simp <;> linarith


/-- The imaginary part of the fundamental mode drops by exactly the
sine-weighted mass of the discrepancy. -/
theorem arcMode_one_im (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2)) :
    (arcMode 1 d).im = 2 - arcCost d := by
  have hchart (i : Fin 4) (t : ℝ) : (chartWave 1 i t).im = -sin t := by
    fin_cases i <;> simp [chartWave, osc_im]
  have h (i : Fin 4) : (∫ t in 0..π/2, d i t • chartWave 1 i t).im =
       -(∫ t in 0..π/2, sin t * d i t) := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (osc_integrable 1 (d i) i (hi i))]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.imCLM_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, hchart]
    ring
  have H := Finset.sum_congr (s₁ := (univ : Finset (Fin 4))) rfl (fun i _ => h i)
  rw [Finset.sum_neg_distrib] at H
  simp only [arcMode, dipoleMode, modeChange, Nat.cast_one, one_smul, Nat.not_even_one, if_false,
    Complex.add_im, Complex.mul_I_im, Complex.re_ofNat, Complex.im_sum, arcCost]
  linarith only [H]

def modeLoss (n : ℕ) (d : Fin 4 → ℝ → ℝ) : ℝ := ‖arcMode n d‖^2 - ‖dipoleMode n‖^2

/-- Every higher harmonic of an interval-integrable occupation pattern has
excess squared amplitude bounded by the same fundamental-mode deficit.
The only orientation requirement here is nonnegative projected first moment. -/
theorem modeLoss_le {n : ℕ} (hn : 2 ≤ n) (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1)
    (hor : 0 ≤ 2 - arcCost d) :
    modeLoss n d ≤ (n:ℝ)^4 * (4 - (2 - arcCost d)^2) := by
  let z := 2 - arcCost d
  have hJ : 0 ≤ arcCost d := Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg
    (by positivity) (fun t ht => mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,pi_pos])) (hd i t ht).1)
  have hz : z ≤ 2 := by dsimp [z]; linarith
  have hJz : 2-z = arcCost d := by dsimp [z]; ring
  have hb : (arcMass d)^2 ≤ 4*π*(2-z) := by rw [hJz]; exact discrepancy_mass_sq_le d hi hd
  have hΔ := pow_le_pow_left₀ (norm_nonneg _) (modeChange_norm n d hi (fun i t ht => (hd i t ht).1)) 2
  rw [mul_pow] at hΔ
  by_cases he : Even n
  · have hzero : dipoleMode n = 0 := if_pos he
    have hU := pow_le_pow_left₀ (norm_nonneg _) (modeChange_norm_even n he d hi hd) 2
    rw [mul_pow] at hU
    simpa [modeLoss, arcMode, hzero, z] using
      even_mode_bound (n := (n:ℝ)) (z := z) (by exact_mod_cast hn) hor hz hb hΔ hU
  · have h3 : 3 ≤ n := by
      have hh : n ≠ 2 := fun h => he (h ▸ even_two)
      omega
    have h2 : dipoleMode n = 2*Complex.I := if_neg he
    have hL := modeChange_im_le n d hi (fun i t ht => (hd i t ht).1)
    have hid : modeLoss n d = 4*(modeChange n d).im + ‖modeChange n d‖^2 := by
      simp [modeLoss, arcMode, h2, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
      ring
    have hh := odd_mode_bound (n := (n:ℝ)) (z := z) (P := modeLoss n d+4)
      (by exact_mod_cast h3) hor hz hb (by rw [hJz, hid]; linarith only [hL, hΔ])
    simpa [z] using hh

/-- Weighted semicircle deficit for the actual Fourier modes of the
four quadrant charts. Alignment makes the projected first moment its norm. -/
theorem arc_semicircle_deficit (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1)
    (hre : (arcMode 1 d).re = 0) (him : 0 ≤ (arcMode 1 d).im)
    (w : ℕ → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw : Summable fun k => w k * ((k+2:ℕ):ℝ)^4)
    (hR : ∑' k, w k * ((k+2:ℕ):ℝ)^4 ≤ 2/3) :
    (4-‖arcMode 1 d‖^2)/3 ≤
        4-‖arcMode 1 d‖^2 - ∑' k, w k * modeLoss (k+2) d := by
  have hs : ‖arcMode 1 d‖ = 2-arcCost d := by
    rw [← arcMode_one_im d hi, Complex.norm_def, Complex.normSq_apply, hre]
    simp [← sq, Real.sqrt_sq him]
  have hJ : 0 ≤ arcCost d := Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg
    (by positivity) (fun t ht => mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,pi_pos])) (hd i t ht).1)
  have hN : 0 ≤ 2-arcCost d := hs ▸ norm_nonneg _
  have hm (k : ℕ) := modeLoss_le (n := k+2) (by omega) d hi hd hN
  have hL : Summable fun k => w k * modeLoss (k+2) d := by
    apply Summable.of_norm_bounded (g := fun k => (w k * ((k+2:ℕ):ℝ)^4)*4) (hw.mul_right _)
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hw0 k)
    have hp : 1 ≤ ((k+2:ℕ):ℝ)^4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k+2 by omega))
    have hbase : ‖dipoleMode (k+2)‖^2 ≤ 4 := by
      unfold dipoleMode
      split <;> norm_num [norm_mul]
    rw [abs_le]
    exact ⟨by unfold modeLoss; linarith only [hp, hbase, sq_nonneg ‖arcMode (k+2) d‖],
      (hm k).trans (mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (2-arcCost d)]) (by positivity))⟩
  rw [hs]
  exact semicircle_deficit_of_mode_bounds hN (by linarith only [hJ]) hw0 hw hL hR hm

#print axioms arc_semicircle_deficit
end GaussianChains.Localization

