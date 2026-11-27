import CertTreeFourierCaps

/-! Appendix A's width perturbation bound, with the reference amplitude held
fixed. The same rational majorant handles the narrow and the two broad slabs. -/
noncomputable section
namespace GaussianChains.WidthBounds

open Real FourierBounds PackedFace

/-- Affine rescaling of the interaction kernel around a reference width. -/
def matched (a s x : ℝ) : ℝ :=
  scale a + (scale a*nome a)/(scale s*nome s)*(kernel s x-scale s)

theorem matched_series {a s : ℝ} (hs : 0 < s) :
    matched a s = fun x => scale a + 2*scale a*nome a * series (nome s) 0 x := by
  funext x
  rw [matched, kernel_series hs]
  have hc : scale s ≠ 0 := (Real.sqrt_pos.mpr (div_pos pi_pos hs)).ne'
  have hq := (nome_positive s).ne'
  dsimp only
  field_simp
  ring

theorem matched_self {a : ℝ} (ha : 0 < a) : matched a a = kernel a := by
  rw [matched_series ha, kernel_series ha]

theorem matched_derivative {a s : ℝ} (hs : 0 < s) (j : ℕ) :
    deriv^[j] (matched a s) = fun x => (if j=0 then scale a else 0) +
      (2*scale a*nome a*(2*π)^j)*series (nome s) j x := by
  induction j with
  | zero => simpa using matched_series (a:=a) hs
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hd := ((series_deriv (nome_positive s).le (nome_lt_one hs) j x).const_mul
      (2*scale a*nome a*(2*π)^j)).const_add (if j=0 then scale a else 0)
    rw [hd.deriv]
    simp only [Nat.succ_ne_zero, if_false, zero_add, pow_succ]
    ring

theorem nome_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : nome s ≤ nome t := by
  apply Real.exp_le_exp.mpr
  rw [div_le_div_iff₀ hs (hs.trans_le hst)]
  exact mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr (sq_nonneg π))

/-- Endpoint estimates for a single normalized Fourier coefficient.
`L,U` enclose the varying nome; `A,B` enclose the reference nome. -/
def discrepancy (L A B U : ℝ) (n : ℕ) : ℝ :=
  max (U^(n^2-1)-A^(n^2-1)) (B^(n^2-1)-L^(n^2-1))

private theorem pow_difference {q p L A B U : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hl : L ≤ q) (hu : q ≤ U) (ha : A ≤ p) (hb : p ≤ B) (n : ℕ) :
    |q^(n^2-1)-p^(n^2-1)| ≤ discrepancy L A B U n := by
  unfold discrepancy
  apply abs_le.mpr
  have hq := hL.trans hl
  have hp := hA.trans ha
  have h₁ := pow_le_pow_left₀ hL hl (n^2-1)
  have h₂ := pow_le_pow_left₀ hq hu (n^2-1)
  have h₃ := pow_le_pow_left₀ hA ha (n^2-1)
  have h₄ := pow_le_pow_left₀ hp hb (n^2-1)
  constructor
  · linarith only [le_max_right (U^(n^2-1)-A^(n^2-1)) (B^(n^2-1)-L^(n^2-1)), h₁, h₄]
  · linarith only [le_max_left (U^(n^2-1)-A^(n^2-1)) (B^(n^2-1)-L^(n^2-1)), h₂, h₃]

private theorem mode_difference {q p D : ℝ} (j n : ℕ) (x : ℝ)
    (h : |q^((n+1)^2-1)-p^((n+1)^2-1)| ≤ D) :
    |mode q j n x-mode p j n x| ≤ ((n+1:ℕ):ℝ)^j*D := by
  simp only [mode, weightedMode, ← sub_mul, ← mul_sub, abs_mul, abs_pow, Nat.abs_cast]
  apply (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Finite modes 1 through 4 and the geometric majorant beginning at mode 5. -/
def widthError (C P L A B U : ℝ) (j : ℕ) : ℝ := (2*C*B*P^j) *
  ((∑ n ∈ Finset.range 4, ((n+1:ℕ):ℝ)^j * discrepancy L A B U (n+1)) +
    5^j * U^24 / (1-tailRatio U j 5))

theorem width_error_sound {a s C P L A B U : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hc : scale a ≤ C) (hP : 2*π ≤ P)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hl : L ≤ nome s) (hu : nome s ≤ U)
    (hal : A ≤ nome a) (hau : nome a ≤ B) (hAU : nome a ≤ U) (hU : U < 1)
    (j : ℕ) (hR : tailRatio U j 5 < 1) (x : ℝ) :
    |deriv^[j] (matched a s) x - deriv^[j] (kernel a) x| ≤ widthError C P L A B U j := by
  let f := fun n : ℕ => mode (nome s) j n x
  let g := fun n : ℕ => mode (nome a) j n x
  have hq := (nome_positive s).le
  have hp := (nome_positive a).le
  have hu0 := hq.trans hu
  have hf : Summable f := mode_summable hq (nome_lt_one hs) j x
  have hg : Summable g := mode_summable hp (nome_lt_one ha) j x
  have hd := hf.sub hg
  have hsplit : series (nome s) j x-series (nome a) j x =
      (∑ n ∈ Finset.range 4, (f n-g n)) + ∑' n : ℕ, (f (n+4)-g (n+4)) := by
    exact (hf.tsum_sub hg).symm.trans (hd.sum_add_tsum_nat_add 4).symm
  have h₁ : |∑ n ∈ Finset.range 4, (f n-g n)| ≤
      ∑ n ∈ Finset.range 4, ((n+1:ℕ):ℝ)^j * discrepancy L A B U (n+1) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun n _ => mode_difference j n x (pow_difference hL hA hl hu hal hau _)
  have hmajor := weightedMode_tail (q:=U) hu0 le_rfl hU.le j 5 (by decide) hR
  have h₂ : |∑' n : ℕ, (f (n+4)-g (n+4))| ≤ 5^j * U^24 / (1-tailRatio U j 5) := by
    have hterm (n : ℕ) : ‖f (n+4)-g (n+4)‖ ≤ weightedMode U j (n+5) := by
      rw [Real.norm_eq_abs]
      apply mode_difference
      apply abs_le.mpr
      have hh1 := pow_le_pow_left₀ hq hu ((n+5)^2-1)
      have hh2 := pow_le_pow_left₀ hp hAU ((n+5)^2-1)
      constructor <;> linarith [pow_nonneg hq ((n+5)^2-1), pow_nonneg hp ((n+5)^2-1)]
    rw [← Real.norm_eq_abs]
    apply (tsum_of_norm_bounded hmajor.1.hasSum hterm).trans
    simpa [weightedMode] using hmajor.2
  have hb := (abs_add_le (∑ n ∈ Finset.range 4, (f n-g n)) (∑' n : ℕ, (f (n+4)-g (n+4)))).trans
    (add_le_add h₁ h₂)
  rw [← hsplit] at hb
  rw [← matched_self ha, matched_derivative hs, matched_derivative ha]
  change |(_ + _ * _) - (_ + _ * _)| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg (by have : 0 ≤ scale a := Real.sqrt_nonneg _; positivity :
      0 ≤ 2*scale a*nome a*(2*π)^j)]
  have hc₀ : 0 ≤ C := (Real.sqrt_nonneg _).trans hc
  have hb₀ := hp.trans hau
  have hP₀ : 0 ≤ P := (by positivity : 0 ≤ 2*π).trans hP
  apply mul_le_mul _ hb (abs_nonneg _) (by positivity)
  gcongr

end GaussianChains.WidthBounds
