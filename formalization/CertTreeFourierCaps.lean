import KernelFourier
import ClustersWidth
import PackedFaceBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Uniform spatial derivative estimates for the periodic Gaussian. Positive
Fourier coefficients allow the absolute second-derivative bound at zero to be
used on every displacement. -/

noncomputable section
namespace GaussianChains.FourierBounds

open Real PackedFace

def nome (s : ℝ) := Real.exp (-(π^2)/s)

def scale (s : ℝ) := Real.sqrt (π/s)

def mode (q : ℝ) (j n : ℕ) (x : ℝ) : ℝ :=
  weightedMode q j (n+1) * cos (2*π*((n+1:ℕ):ℝ)*x+(j:ℝ)*π/2)

def series (q : ℝ) (j : ℕ) (x : ℝ) := ∑' n : ℕ, mode q j n x

theorem weights_summable {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Summable (fun n : ℕ => weightedMode q j (n+1)) := by
  apply (summable_nat_add_iff 1).mp
  simpa [weightedMode, Nat.add_assoc] using summable_widthMoment j hq hq1

private theorem mode_bound {q : ℝ} (hq : 0 ≤ q) (j n : ℕ) (x : ℝ) :
    |mode q j n x| ≤ weightedMode q j (n+1) := by
  rw [mode, abs_mul, abs_of_nonneg (weightedMode_nonneg hq _ _)]
  exact mul_le_of_le_one_right (weightedMode_nonneg hq _ _) (abs_cos_le_one _)

theorem mode_summable {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (x : ℝ) :
    Summable (fun n : ℕ => mode q j n x) :=
  .of_norm_bounded (weights_summable hq hq1 j) fun n => by
    simpa only [Real.norm_eq_abs] using mode_bound hq j n x

private theorem mode_deriv (q : ℝ) (j n : ℕ) (x : ℝ) :
    HasDerivAt (mode q j n) ((2*π)*mode q (j+1) n x) x := by
  let ω := 2*π*((n+1:ℕ):ℝ)
  let θ := (j:ℝ)*π/2
  have hd := ((((hasDerivAt_id x).const_mul ω).add_const θ).cos).const_mul (weightedMode q j (n+1))
  convert hd using 1
  have hφ : ω*x+((j+1:ℕ):ℝ)*π/2 = (ω*x+θ)+π/2 := by dsimp [θ]; push_cast; ring
  change 2*π*(weightedMode q (j+1) (n+1)*cos (ω*x+((j+1:ℕ):ℝ)*π/2)) = _
  rw [hφ, Real.cos_add_pi_div_two]
  simp [weightedMode, pow_succ, ω, θ]
  ring

theorem series_deriv {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (x : ℝ) :
    HasDerivAt (series q j) (2*π*series q (j+1) x) x := by
  have h := hasDerivAt_tsum ((weights_summable hq hq1 (j+1)).mul_left (2*π))
    (mode_deriv q j) (fun n y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*π)]
      exact mul_le_mul_of_nonneg_left (mode_bound hq _ n y) (by positivity))
    (mode_summable hq hq1 j 0) x
  simpa only [series, tsum_mul_left] using h

theorem kernel_series {s : ℝ} (hs : 0 < s) :
    GaussianChains.kernel s = fun x => scale s + (2*scale s*nome s)*series (nome s) 0 x := by
  funext x
  rw [kernel_fourier hs]
  have hterms : (∑' n : ℕ, nome s ^ ((n+1)^2) * cos (2*π*((n+1:ℕ):ℝ)*x)) =
      nome s * series (nome s) 0 x := by
    rw [series, ← tsum_mul_left]
    apply tsum_congr
    intro n
    have hn : 0 < (n+1)^2 := by positivity
    have hp : (n+1)^2 = ((n+1)^2-1)+1 := by omega
    simp only [mode, weightedMode, pow_zero, one_mul, Nat.cast_zero, zero_mul, zero_div, add_zero]
    rw [← mul_assoc, mul_comm (nome s), ← pow_succ, ← hp]
  change scale s * (1+2*(∑' n : ℕ, nome s ^ ((n+1)^2) * cos (2*π*((n+1:ℕ):ℝ)*x))) = _
  rw [hterms]
  ring

theorem nome_positive (s : ℝ) : 0 < nome s := Real.exp_pos _

theorem nome_lt_one {s : ℝ} (hs : 0 < s) : nome s < 1 :=
  Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos pi_pos)) hs)

theorem kernel_deriv_series {s : ℝ} (hs : 0 < s) (n : ℕ) :
    deriv^[n+1] (GaussianChains.kernel s) =
      fun x => (2*scale s*nome s*(2*π)^(n+1))*series (nome s) (n+1) x := by
  have hq := (nome_positive s).le
  have hq1 := nome_lt_one hs
  induction n with
  | zero =>
    rw [kernel_series hs]
    funext x
    have hd := ((series_deriv hq hq1 0 x).const_mul (2*scale s*nome s)).const_add (scale s)
    simpa only [Function.iterate_one, zero_add, pow_one, ← mul_assoc] using hd.deriv
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hd := (series_deriv hq hq1 (n+1) x).const_mul (2*scale s*nome s*(2*π)^(n+1))
    rw [hd.deriv, pow_succ (2*π) (n+1)]
    ring

private theorem abs_series_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (x : ℝ) :
    |series q j x| ≤ ∑' n : ℕ, weightedMode q j (n+1) := by
  have h := (mode_summable hq hq1 j x).norm
  refine (show |series q j x| ≤ ∑' n : ℕ, ‖mode q j n x‖ by
    simpa only [series, Real.norm_eq_abs] using norm_tsum_le_tsum_norm h).trans ?_
  exact h.tsum_le_tsum (fun n => by simpa only [Real.norm_eq_abs] using mode_bound hq j n x)
    (weights_summable hq hq1 j)

/-- Rational-cap interface. Split out the fundamental, majorize the rest by
the geometric ratio obtained at the second harmonic. -/
theorem derivative_cap {s Q C P : ℝ} (hs : 0 < s) (hQ : nome s ≤ Q) (hQ1 : Q ≤ 1)
    (hC : scale s ≤ C) (hP : 2*π ≤ P) (j : ℕ) (hr : tailRatio Q (j+1) 2 < 1) (x : ℝ) :
    |deriv^[j+1] (GaussianChains.kernel s) x| ≤
      (2*C*Q*P^(j+1)) * (1 + 2^(j+1)*Q^3/(1-tailRatio Q (j+1) 2)) := by
  have hq := (nome_positive s).le
  have hw := weights_summable hq (nome_lt_one hs) (j+1)
  have h0 : 0 ≤ scale s := Real.sqrt_nonneg _
  have hCC : 0 ≤ C := h0.trans hC
  have hQQ : 0 ≤ Q := hq.trans hQ
  have hPP : 0 ≤ P := (by positivity : 0 ≤ 2*π).trans hP
  have htail := (weightedMode_tail hq hQ hQ1 (j+1) 2 (by decide) hr).2
  have hb : |series (nome s) (j+1) x| ≤ 1 + 2^(j+1)*Q^3/(1-tailRatio Q (j+1) 2) := by
    apply (abs_series_le hq (nome_lt_one hs) (j+1) x).trans
    rw [hw.tsum_eq_zero_add]
    have ht : weightedMode (nome s) (j+1) 2 = 2^(j+1)*(nome s)^3 := by norm_num [weightedMode]
    rw [ht] at htail
    simp only [zero_add, weightedMode, Nat.cast_one, one_pow, Nat.sub_self, pow_zero, mul_one]
    apply add_le_add le_rfl
    apply htail.trans
    have hden := sub_pos.mpr hr
    gcongr
  rw [kernel_deriv_series hs j, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*scale s*nome s*(2*π)^(j+1))]
  apply mul_le_mul _ hb (abs_nonneg _) (by positivity)
  gcongr

/-- The three spatial tables on the broad width strip. -/
theorem strip_derivative_caps {s : ℝ} (hs : s ∈ Set.Icc (8:ℝ) 9) (x : ℝ) :
    |deriv (GaussianChains.kernel s) x| < 4 ∧
    |deriv^[2] (GaussianChains.kernel s) x| < 20 ∧
    |deriv^[3] (GaussianChains.kernel s) x| < 150 := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hq : nome s ≤ 17/50 := by simpa [nome, neg_div] using (nome_lt_seventeen_fiftieths hs0 hs.2).le
  have hc : scale s ≤ 63/100 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, (div_le_iff₀ hs0).mpr ?_⟩
    linarith [hs.1, Real.pi_lt_d2]
  have hp : 2*π ≤ 63/10 := by linarith [Real.pi_lt_d2]
  have h1 := derivative_cap hs0 hq (by norm_num) hc hp 0 (by norm_num [tailRatio]) x
  have h2 := derivative_cap hs0 hq (by norm_num) hc hp 1 (by norm_num [tailRatio]) x
  have h3 := derivative_cap hs0 hq (by norm_num) hc hp 2 (by norm_num [tailRatio]) x
  exact ⟨h1.trans_lt (by norm_num [tailRatio]), h2.trans_lt (by norm_num [tailRatio]),
    h3.trans_lt (by norm_num [tailRatio])⟩

private theorem point_nome : nome 22 ≤ 2/3 := by
  have ha := Real.sum_le_exp_of_nonneg (x := 9/22) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at ha
  have hlarge : (3/2:ℝ) ≤ Real.exp (π^2/22) := by
    apply (show (3/2:ℝ) ≤ Real.exp (9/22) by linarith).trans
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three, sq_nonneg (π-3)]
  rw [nome, neg_div, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- Third and fourth derivative constants for the independent block-word atlas. -/
theorem point_high_derivative_caps (x : ℝ) :
    |deriv^[3] (GaussianChains.kernel 22) x| < 1500 ∧
    |deriv^[4] (GaussianChains.kernel 22) x| < 22000 := by
  have hc : scale 22 ≤ 1/2 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    linarith [Real.pi_lt_d2]
  have hp : 2*π ≤ 63/10 := by linarith [Real.pi_lt_d2]
  have h3 := derivative_cap (by norm_num) point_nome (by norm_num) hc hp 2 (by norm_num [tailRatio]) x
  have h4 := derivative_cap (by norm_num) point_nome (by norm_num) hc hp 3 (by norm_num [tailRatio]) x
  exact ⟨h3.trans_lt (by norm_num [tailRatio]), h4.trans_lt (by norm_num [tailRatio])⟩

/-- The absolute second derivative is bounded by its absolute value at zero:
at zero all cosine coefficients of the second derivative have the same sign. -/
theorem curvature_max_at_zero {s : ℝ} (hs : 0 < s) (x : ℝ) :
    |deriv^[2] (GaussianChains.kernel s) x| ≤ -deriv^[2] (GaussianChains.kernel s) 0 := by
  have hq := (nome_positive s).le
  have hscale : 0 ≤ scale s := Real.sqrt_nonneg _
  have hz : series (nome s) 2 0 = -(∑' n : ℕ, weightedMode (nome s) 2 (n+1)) := by
    simp [series, mode, Real.cos_pi, tsum_neg]
  rw [kernel_deriv_series hs 1, abs_mul, abs_of_nonneg (by positivity : 0 ≤
    2*scale s*nome s*(2*π)^2)]
  change _ ≤ -(2*scale s*nome s*(2*π)^2*series (nome s) 2 0)
  rw [hz, mul_neg, neg_neg]
  exact mul_le_mul_of_nonneg_left (abs_series_le hq (nome_lt_one hs) 2 x) (by positivity)

end GaussianChains.FourierBounds
