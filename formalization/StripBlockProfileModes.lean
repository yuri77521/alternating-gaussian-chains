import ClusterSeriesAmplitude
import StripMultipliers

/-! Finite complex sums of centered blocks with one through four labels. -/
noncomputable section
namespace GaussianChains.Strip
open Real ClusterSeries

def centeredModeSum (b : Fin 4) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (b.val+1), (-1:ℂ)^j * phase (((j:ℝ)-(b.val:ℝ)/2)*w)

private theorem phase_pair_plus (u : ℝ) : phase (-u) + phase u = 2 * (cos u : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [phase,Complex.ofReal_neg]
  ring

private theorem phase_pair_minus (u : ℝ) : phase (-u) - phase u = -2 * (sin u : ℂ) * Complex.I := by
  apply Complex.ext <;> simp only [phase,Complex.sub_re,Complex.sub_im,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,cos_neg,sin_neg,
    Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im] <;> norm_num <;> ring

theorem centeredModeSum_eq (b : Fin 4) (w : ℝ) :
    centeredModeSum b w = (blockMultiplier b w:ℂ) *
      (if b.val%2=1 then -Complex.I else 1) := by
  have h0 : phase 0 = 1 := by simp [phase]
  fin_cases b
  · norm_num [centeredModeSum,Finset.sum_range_succ,blockMultiplier,h0]
  · convert phase_pair_minus (w/2) using 1 <;>
      norm_num [centeredModeSum,Finset.sum_range_succ,blockMultiplier] <;> ring_nf
  · have h := phase_pair_plus w
    rw [Complex.ofReal_cos] at h
    norm_num [centeredModeSum,Finset.sum_range_succ,blockMultiplier,h0]
    linear_combination h
  · have ht : sin (3*w/2)-sin (w/2) = 2*sin (w/2)*cos w := by
      rw [sin_sub_sin]
      rw [show (3*w/2-w/2)/2=w/2 by ring,show (3*w/2+w/2)/2=w by ring]
    have h₃ := phase_pair_minus (3*w/2)
    have h₁ := phase_pair_minus (w/2)
    have hsin := congrArg Complex.ofReal ht
    push_cast at h₃ h₁ hsin
    norm_num [centeredModeSum,Finset.sum_range_succ,blockMultiplier]
    ring_nf at h₃ h₁ hsin ⊢
    linear_combination h₃ - h₁ - 2*Complex.I*hsin

end GaussianChains.Strip
