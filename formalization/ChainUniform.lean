import CertTreeFourierCaps
import ClustersWidthPhysical
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Absolute uniform convergence of all spatial Fourier derivatives of the
period-one Gaussian on every positive closed width interval and the entire
real displacement axis. The zeroth frequency includes the original constant. -/

noncomputable section
namespace GaussianChains
open Real FourierBounds PackedFace Filter

/-- Fourier summand of the j-th derivative in the period-one position x.
For n>0 its coefficient is 2 sqrt(π/s) q^(n²) (2πn)^j; differentiating
cosine shifts the phase by jπ/2. -/
def spatialFourierTerm (j : ℕ) : ℕ → ℝ × ℝ → ℝ
  | 0, w => if j = 0 then scale w.1 else 0
  | n+1, w => (2*scale w.1*nome w.1*(2*π)^j) * mode (nome w.1) j n w.2

private def spatialMajorant (j : ℕ) (s₀ S : ℝ) : ℕ → ℝ
  | 0 => scale s₀
  | n+1 => (2*scale s₀*nome S*(2*π)^j) * weightedMode (nome S) j (n+1)

private theorem summable_spatialMajorant (j : ℕ) (s₀ : ℝ) {S : ℝ} (hS : 0 < S) :
    Summable (spatialMajorant j s₀ S) := by
  apply (summable_nat_add_iff (f:=spatialMajorant j s₀ S) 1).mp
  exact (weights_summable (nome_positive S).le (nome_lt_one hS) j).mul_left _

private theorem spatialTerm_le (j n : ℕ) {s₀ S s : ℝ} (h₀ : 0 < s₀)
    (hs : s ∈ Set.Icc s₀ S) (x : ℝ) :
    ‖spatialFourierTerm j n (s,x)‖ ≤ spatialMajorant j s₀ S n := by
  have hpos := h₀.trans_le hs.1
  have hc : scale s ≤ scale s₀ :=
    sqrt_le_sqrt (div_le_div_of_nonneg_left pi_pos.le h₀ hs.1)
  have hq : nome s ≤ nome S := by
    apply exp_le_exp.mpr
    simp only [neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg π) hpos hs.2)
  have hc0 : 0 ≤ scale s := sqrt_nonneg _
  have hc₀ : 0 ≤ scale s₀ := sqrt_nonneg _
  have hq0 := (nome_positive s).le
  have hqS := (nome_positive S).le
  cases n with
  | zero =>
    simp only [spatialFourierTerm,spatialMajorant]
    split_ifs <;> simp only [Real.norm_eq_abs,abs_of_nonneg hc0,norm_zero] <;> assumption
  | succ n =>
    have hw : weightedMode (nome s) j (n+1) ≤ weightedMode (nome S) j (n+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) (by positivity)
    have hm : ‖mode (nome s) j n x‖ ≤ weightedMode (nome S) j (n+1) := by
      rw [Real.norm_eq_abs,mode,abs_mul,abs_of_nonneg (weightedMode_nonneg hq0 _ _)]
      exact (mul_le_of_le_one_right (weightedMode_nonneg hq0 _ _) (abs_cos_le_one _)).trans hw
    have hfac : 2*scale s*nome s*(2*π)^j ≤ 2*scale s₀*nome S*(2*π)^j := by
      gcongr
    simp only [spatialFourierTerm,spatialMajorant]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 2*scale s*nome s*(2*π)^j by positivity)]
    exact mul_le_mul hfac hm (norm_nonneg _) (by positivity)

private theorem series_zero_angularK {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : ℝ) :
    series q 0 x = angularK q (2*π*x) := by
  rw [series,(mode_summable hq0 hq1 0 x).tsum_eq_zero_add,angularK_eq]
  have hfirst : mode q 0 0 x = cos (2*π*x) := by norm_num [mode,weightedMode]
  rw [hfirst]
  apply congrArg (cos (2*π*x) + ·)
  apply tsum_congr
  intro k
  simp only [mode,weightedMode,pow_zero,one_mul,Nat.cast_zero,zero_mul,zero_div,add_zero]
  congr 2
  ring

theorem spatialFourierTerm_hasSum (j : ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasSum (fun n => spatialFourierTerm j n (s,x)) (iteratedDeriv j (kernel s) x) := by
  have hm := summable_spatialMajorant j s hs
  have hss : s ∈ Set.Icc s s := ⟨le_rfl,le_rfl⟩
  have hsum : Summable (fun n => spatialFourierTerm j n (s,x)) :=
    Summable.of_norm_bounded hm (fun n => spatialTerm_le j n hs hss x)
  apply hsum.hasSum_iff.mpr
  rw [hsum.tsum_eq_zero_add,iteratedDeriv_eq_iterate]
  change (if j=0 then scale s else 0) +
    ∑' n, (2*scale s*nome s*(2*π)^j)*mode (nome s) j n x = _
  rw [tsum_mul_left]
  cases j with
  | zero =>
    rw [Function.iterate_zero_apply,kernel_eq_angularK hs]
    change (if (0:ℕ)=0 then scale s else 0) + (2*scale s*nome s*(2*π)^0)*series (nome s) 0 x =
      scale s*(1+2*nome s*angularK (nome s) (2*π*x))
    rw [series_zero_angularK (nome_positive s).le (nome_lt_one hs)]
    simp only [if_true,pow_zero,mul_one]
    ring
  | succ j =>
    simp only [Nat.succ_ne_zero,if_false,zero_add,kernel_deriv_series hs,series]

/-- The natural partial sums converge uniformly to the actual spatial
derivative, and the sums of absolute values converge uniformly as well.
The same summable bound holds jointly for s₀ ≤ s ≤ S and all real x. -/
theorem kernel_fourier_derivatives_uniform (j : ℕ) {s₀ S : ℝ} (h₀ : 0 < s₀) (hS : s₀ ≤ S) :
    let D := {w : ℝ × ℝ | w.1 ∈ Set.Icc s₀ S}
    TendstoUniformlyOn (fun M w => ∑ n ∈ Finset.range M, spatialFourierTerm j n w)
      (fun w => iteratedDeriv j (kernel w.1) w.2) atTop D ∧
    TendstoUniformlyOn (fun M w => ∑ n ∈ Finset.range M, |spatialFourierTerm j n w|)
      (fun w => ∑' n, |spatialFourierTerm j n w|) atTop D ∧
    ∀ w ∈ D, Summable (fun n => |spatialFourierTerm j n w|) := by
  let D := {w : ℝ × ℝ | w.1 ∈ Set.Icc s₀ S}
  have hm := summable_spatialMajorant j s₀ (h₀.trans_le hS)
  have hb (n : ℕ) (w : ℝ × ℝ) (hw : w ∈ D) :
      ‖spatialFourierTerm j n w‖ ≤ spatialMajorant j s₀ S n :=
    spatialTerm_le j n h₀ hw w.2
  have ha (n : ℕ) (w : ℝ × ℝ) (hw : w ∈ D) :
      ‖|spatialFourierTerm j n w|‖ ≤ spatialMajorant j s₀ S n := by
    simpa only [Real.norm_eq_abs,abs_abs] using hb n w hw
  refine ⟨(tendstoUniformlyOn_tsum_nat hm hb).congr_right ?_,
    tendstoUniformlyOn_tsum_nat hm ha,fun w hw => ?_⟩
  · intro w hw
    exact (spatialFourierTerm_hasSum j (h₀.trans_le hw.1) w.2).tsum_eq
  · exact Summable.of_norm_bounded hm (fun n => ha n w hw)

#print axioms spatialFourierTerm_hasSum
#print axioms kernel_fourier_derivatives_uniform
end GaussianChains
