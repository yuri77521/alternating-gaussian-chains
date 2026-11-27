import Mathlib.Analysis.Complex.ExponentialBounds
import Point22Curvature
import CertRootDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Global second derivative bound at width 22 by splitting off the two nearest
images. It applies to the full real displacement line by reindexing the period. -/
noncomputable section
namespace GaussianChains.Root22

private theorem exp_three_halves : (88:ℝ) / 21 ≤ Real.exp (3/2) := by
  have hsq : Real.exp (3/2)^2 = Real.exp 1 ^3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlow : (27/10:ℝ)^3 ≤ Real.exp 1 ^3 := by
    apply pow_le_pow_left₀ (by norm_num)
    linarith [Real.exp_one_gt_d9]
  by_contra! h
  have hh := mul_nonneg (sub_nonneg.mpr h.le) (by positivity : 0 ≤ 88/21 + Real.exp (3/2))
  nlinarith

theorem secondImage_le (u : ℝ) : secondImage u ≤ 21 := by
  let y := 22*u^2
  have h := Real.add_one_le_exp (y-3/2)
  calc
    secondImage u = (88*(y-3/2+1))*Real.exp (-y) := by dsimp [secondImage, y]; ring_nf
    _ ≤ (88*Real.exp (y-3/2))*Real.exp (-y) := by gcongr
    _ = 88 / Real.exp (3/2) := by
      rw [mul_assoc, ← Real.exp_add, show y - 3/2 + -y = -(3/2) by ring,
        Real.exp_neg]
      ring
    _ ≤ 21 := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith [exp_three_halves]

theorem secondImage_ge (u : ℝ) : -44 ≤ secondImage u := by
  have h : Real.exp (-22*u^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  unfold secondImage
  nlinarith [mul_nonneg (sq_nonneg u) (Real.exp_nonneg (-22*u^2))]



private theorem positive_nearest {u : ℝ} (h : 1/2 ≤ |u|) (h' : |u| ≤ 1) :
    Real.exp (-22) ≤ secondImage u := by
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h 2
  have hu := pow_le_pow_left₀ (abs_nonneg _) h' 2
  rw [sq_abs] at hl hu
  unfold secondImage
  calc
    Real.exp (-22) ≤ Real.exp (-22*u^2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := by
      apply le_mul_of_one_le_left (Real.exp_nonneg _)
      nlinarith

theorem curvatureSum_bound_cell {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |curvatureSum x| ≤ 44 - Real.exp (-22) := by
  have hrs := Point22.Curvature.kernel₂_two_images hx
  have hnn := Point22.Curvature.kernel₂_two_images_nonneg hx
  change |curvatureSum x - (secondImage x + secondImage (x-1))| ≤ 1/100 at hrs
  change 0 ≤ curvatureSum x - (secondImage x + secondImage (x-1)) at hnn
  have hbase : -44 + Real.exp (-22) ≤ secondImage x + secondImage (x-1) := by
    by_cases h : 1/2 ≤ x
    · have hb := positive_nearest (h.trans (le_abs_self _)) (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
      linarith [secondImage_ge (x-1)]
    · have hn : 1/2 ≤ |x-1| := (by linarith : 1/2 ≤ -(x-1)).trans (neg_le_abs _)
      have hb := positive_nearest hn (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩)
      linarith [secondImage_ge x]
  rw [abs_le]
  constructor <;> linarith [(abs_le.mp hrs).2, secondImage_le x, secondImage_le (x-1),
    Real.exp_le_one_iff.mpr (by norm_num : (-22:ℝ) ≤ 0)]

theorem curvatureSum_add_int (x : ℝ) (m : ℤ) : curvatureSum (x+m) = curvatureSum x := by
  unfold curvatureSum
  convert (Equiv.addLeft m).tsum_eq (fun k : ℤ => secondImage (x+k)) using 1
  apply tsum_congr
  intro k
  simp [add_assoc]

theorem curvatureSum_uniform (x : ℝ) : |curvatureSum x| ≤ 44 - Real.exp (-22) := by
  rw [← Int.fract_add_floor x, curvatureSum_add_int]
  exact curvatureSum_bound_cell ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem curvatureSum_bound (x : ℝ) : |curvatureSum x| ≤ 44 :=
  (curvatureSum_uniform x).trans (by linarith [Real.exp_pos (-22)])

theorem kernel22_second_deriv_bound (x : ℝ) :
    |deriv (deriv (GaussianChains.kernel 22)) x| ≤ 44 := by
  rw [← curvatureSum_eq_deriv2]
  exact curvatureSum_bound x

theorem derivKernel_lipschitz (x y : ℝ) :
    |derivKernel x - derivKernel y| ≤ 44 * |x-y| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (C := 44) (f := derivKernel) (fun z _ => (hasDerivAt_derivKernel z).differentiableAt)
    (fun z _ => (by rw [(hasDerivAt_derivKernel z).deriv, Real.norm_eq_abs]; exact curvatureSum_bound z))
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

end GaussianChains.Root22

