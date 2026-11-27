import CertRootTail
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Comparisons for the convergence and monotonicity estimates on a half-period. -/
noncomputable section
namespace GaussianChains.Root22

/-- Comparing the two images at positive distances u,v uses only the tangent
lower bound exp(z) ≥ 1+z. -/
private theorem flux_comparison {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (h : 1 ≤ 22*u*(v+u)) :
    v * Real.exp (-22*v^2) ≤ u * Real.exp (-22*u^2) := by
  let z := 22*(v^2-u^2)
  have h' : v ≤ u*(1+z) := by
    dsimp [z]
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr h)]
  calc
    _ ≤ (u*(1+z)) * Real.exp (-22*v^2) := by gcongr
    _ ≤ (u*Real.exp z) * Real.exp (-22*v^2) := by
      gcongr
      linarith [Real.add_one_le_exp z]
    _ = u * Real.exp (-22*u^2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [z]
      ring

theorem derivKernel_nonpos_pairs {x : ℝ} (hs : Summable (term x))
    (hxl : 1/22 ≤ x) (hxu : x ≤ 1/2) : derivKernel x ≤ 0 := by
  unfold derivKernel
  rw [← tsum_nat_add_neg_add_one hs]
  apply tsum_nonpos
  intro n
  let u := x+(n:ℝ)
  let v := (n:ℝ)+1-x
  have hu : 1 ≤ 22*u := by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hv : 1 ≤ v+u := by dsimp [u,v]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hc := flux_comparison (u := u) (v := v) (by linarith)
    (by dsimp [u,v]; linarith) (one_le_mul_of_one_le_of_one_le hu hv)
  dsimp [u,v] at hc
  simp only [term, image, Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one]
  rw [show x + -((n:ℝ)+1) = -((n:ℝ)+1-x) by ring, neg_sq]
  linarith

theorem derivKernel_add_int (x : ℝ) (m : ℤ) : derivKernel (x+m) = derivKernel x := by
  unfold derivKernel
  convert (Equiv.addLeft m).tsum_eq (term x) using 1
  apply tsum_congr
  intro k
  simp [term, image, add_assoc]

theorem derivKernel_zero : derivKernel 0 = 0 := by
  have h := derivKernel_one_sub 0
  have hp := derivKernel_add_int 0 1
  norm_num at h hp
  linarith

theorem derivKernel_half : derivKernel (1/2) = 0 := by
  have h := derivKernel_one_sub (1/2)
  norm_num at h
  linarith

/-- Both endpoints of the exponential chord lie below the affine coefficient
of the Gaussian second derivative. -/
theorem exp_le_curvature_coeff {u : ℝ} (hu : u ∈ Set.Icc (1/4:ℝ) (1/2)) :
    Real.exp (22*u^2) ≤ 1936*u^2 - 44 := by
  have lo : (1/16:ℝ) ≤ u^2 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hu.1 2]
  have hi : u^2 ≤ (1/4:ℝ) := by
    nlinarith [pow_le_pow_left₀ (by linarith [hu.1] : (0:ℝ) ≤ u) hu.2 2]
  let a := (1/4-u^2)*(16/3)
  let b := (u^2-1/16)*(16/3)
  have ha : 0 ≤ a := mul_nonneg (sub_nonneg.mpr hi) (by norm_num)
  have hb : 0 ≤ b := mul_nonneg (sub_nonneg.mpr lo) (by norm_num)
  have hw : a+b=1 := by dsimp [a,b]; ring
  have hc := convexOn_exp.2 (Set.mem_univ (11/8:ℝ)) (Set.mem_univ (11/2:ℝ)) ha hb hw
  simp only [smul_eq_mul] at hc
  have he (n : ℕ) : Real.exp (n:ℝ) ≤ (11/4:ℝ)^n := by
    simpa only [mul_one] using (Real.exp_nat_mul 1 n).le.trans
      (pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) n)
  have h₀ : Real.exp (11/8) ≤ 77 := by
    apply (Real.exp_le_exp.mpr (by norm_num : (11/8:ℝ) ≤ 2)).trans
    exact (he 2).trans (by norm_num)
  have h₁ : Real.exp (11/2) ≤ 440 := by
    apply (Real.exp_le_exp.mpr (by norm_num : (11/2:ℝ) ≤ 6)).trans
    exact (he 6).trans (by norm_num)
  calc
    _ = Real.exp (a*(11/8)+b*(11/2)) := by congr 1; dsimp [a,b]; ring
    _ ≤ _ := hc
    _ ≤ a*77+b*440 := by gcongr
    _ = _ := by dsimp [a,b]; ring

end GaussianChains.Root22
