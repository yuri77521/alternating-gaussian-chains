import CertRootCurvature
import CertRootFlux
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Half-period estimates for the two residual opposite charges at width 22. -/
noncomputable section
namespace GaussianChains.Root22
open Set

theorem antitoneOn_interval_of_slope {a b : ℝ} {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (h : ∀ x ∈ Icc a b, D x ≤ 0) : AntitoneOn f (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => h x (interior_subset hx))

private theorem near_curvature {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/22)) : curvatureSum x ≤ 0 := by
  have hi : x^2 ≤ (1/22:ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 _
  have he : 21/22 ≤ Real.exp (-22*x^2) := by linarith [Real.add_one_le_exp (-22*x^2)]
  have hm : secondImage x ≤ -30 := by
    unfold secondImage
    have h1 : 1936*x^2-44 ≤ -40 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-22*x^2))
    linarith
  have htail := (abs_le.mp (Point22.Curvature.kernel₂_two_images (x:=x)
    ⟨hx.1, by linarith [hx.2]⟩)).2
  change curvatureSum x - (secondImage x + secondImage (x-1)) ≤ _ at htail
  linarith [secondImage_le (x-1)]

theorem derivKernel_nonpos {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/2)) : derivKernel x ≤ 0 := by
  by_cases h : 1/22 ≤ x
  · exact derivKernel_nonpos_pairs (derivKernel_summable x) h hx.2
  · have hsmall := antitoneOn_interval_of_slope hasDerivAt_derivKernel (fun z hz => near_curvature hz)
    have hle := hsmall (show (0:ℝ) ∈ Icc (0:ℝ) (1/22) by norm_num)
      (show x ∈ Icc (0:ℝ) (1/22) from ⟨hx.1, by linarith⟩) hx.1
    simpa [derivKernel_zero] using hle

theorem kernel_antitoneOn_half : AntitoneOn (GaussianChains.kernel 22) (Icc (0:ℝ) (1/2)) :=
  antitoneOn_interval_of_slope hasDerivAt_kernel22 (fun x hx => derivKernel_nonpos hx)

theorem curvatureSum_ge_one {x : ℝ} (hx : x ∈ Icc (1/4:ℝ) (1/2)) : 1 ≤ curvatureSum x := by
  have hpos := Real.exp_pos (22*x^2)
  have hc := exp_le_curvature_coeff hx
  have hmain : 1 ≤ secondImage x := by
    unfold secondImage
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ hpos).mpr (by simpa using hc)
  have hother : 0 ≤ secondImage (x-1) := by
    unfold secondImage
    apply mul_nonneg _ (Real.exp_nonneg _)
    nlinarith [mul_nonneg (show 0 ≤ 1/2-x by linarith [hx.2]) (show 0 ≤ 3/2-x by linarith [hx.2])]
  have hn := Point22.Curvature.kernel₂_two_images_nonneg (x:=x) (show x ∈ Icc (0:ℝ) 1 from
    ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  change 0 ≤ curvatureSum x - (secondImage x + secondImage (x-1)) at hn
  linarith

theorem derivKernel_le_displacement {x : ℝ} (hx : x ∈ Icc (1/4:ℝ) (1/2)) :
    derivKernel x ≤ x-1/2 := by
  let f (y : ℝ) := y - derivKernel y
  have h (y : ℝ) : HasDerivAt f (1-curvatureSum y) y :=
    (hasDerivAt_id y).sub (hasDerivAt_derivKernel y)
  have ha := antitoneOn_interval_of_slope h (a := 1/4) (b := 1/2) (fun z hz => sub_nonpos.mpr (curvatureSum_ge_one hz))
  have hb := ha hx (show (1/2:ℝ) ∈ Icc (1/4:ℝ) (1/2) by norm_num) hx.2
  dsimp [f] at hb
  rw [derivKernel_half] at hb
  linarith

end GaussianChains.Root22
