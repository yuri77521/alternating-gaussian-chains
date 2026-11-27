import PackedFaceBoundsSigns
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv

/-! Uniform convergence on the closed interval, and termwise differentiation on its interior. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set Polynomial.Chebyshev

private def major (q : ℝ) (k : ℕ) : ℝ := 18 * weightedMode q 4 (k+1)

private theorem summable_major {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) : Summable (major q) := by
  have hs : Summable (fun k : ℕ => weightedMode q 4 (k+1)) := by
    rw [← summable_nat_add_iff 2]
    exact (fourth_tail_bound hq hQ).1
  exact hs.mul_left 18

private theorem amp_sq (h : ℝ) (n : ℕ) : amplitude h n^2 ≤ 9 := by
  have h₁ := pow_le_pow_left₀ (abs_nonneg _) (abs_amplitude_le h n) 2
  simpa only [sq_abs] using h₁.trans_eq (by norm_num : (3:ℝ)^2 = 9)

private theorem mode_major {q h y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Icc 0 2) (k : ℕ) :
    ‖phiMode q h y (k+1)‖ ≤ major q k := by
  let n := k+1
  have hn : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by dsimp [n]; omega : 1 ≤ n)
  have hp : (1:ℝ) ≤ (n:ℝ)^4 := one_le_pow₀ hn
  have hT := abs_eval_T (n:ℤ) (show 1-y ∈ Icc (-1) 1 by constructor <;> linarith [hy.1,hy.2])
  have hb : |(T ℝ n).eval (1-y)-1| ≤ 2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hT
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  change ‖phiMode q h y n‖ ≤ 18 * weightedMode q 4 n
  simp only [Real.norm_eq_abs, phiMode, abs_mul, abs_pow, abs_neg, abs_one,one_pow,one_mul,
    abs_of_nonneg hq,sq_abs,weightedMode]
  calc
    _ ≤ (q^(n^2-1)*9)*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left (amp_sq h n) (pow_nonneg hq _)) hb (abs_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (pow_nonneg hq (n^2-1))]

private theorem modeD_major {q h y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Icc 0 2) (k : ℕ) :
    ‖phiModeD q h y (k+1)‖ ≤ major q k := by
  rw [Real.norm_eq_abs]
  refine (modeD_bound hq hy _).trans ?_
  have hn : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (by omega : 1 ≤ k+1)
  have hpow := pow_le_pow_right₀ hn (by decide : 2 ≤ 4)
  unfold major weightedMode
  exact mul_le_mul ((amp_sq _ _).trans (by norm_num))
    (mul_le_mul_of_nonneg_right hpow (pow_nonneg hq _)) (by positivity) (by norm_num)

private theorem modeDD_major {q h y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Icc 0 2) (k : ℕ) :
    ‖phiModeDD q h y (k+1)‖ ≤ major q k := by
  rw [Real.norm_eq_abs]
  exact (modeDD_bound hq hy (k+1)).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (weightedMode_nonneg hq 4 _))

theorem continuousOn_phi {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    ContinuousOn (phi q h) (Icc 0 2) :=
  continuousOn_tsum (fun k y _ => (hasDerivAt_phiMode q h y (k+1)).continuousAt.continuousWithinAt)
    (summable_major hq hQ) (fun k _ hy => mode_major hq hy k)

theorem continuousOn_phiD {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    ContinuousOn (phiD q h) (Icc 0 2) :=
  continuousOn_tsum (fun k y _ => (hasDerivAt_phiModeD q h y (k+1)).continuousAt.continuousWithinAt)
    (summable_major hq hQ) (fun k _ hy => modeD_major hq hy k)

theorem continuousOn_phiDD {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    ContinuousOn (phiDD q h) (Icc 0 2) := by
  apply continuousOn_tsum (u := major q) _ (summable_major hq hQ) (fun k _ hy => modeDD_major hq hy k)
  intro k y _
  have hi := (hasDerivAt_id y).const_sub (1:ℝ)
  have hd := ((T ℝ (k+1:ℕ)).derivative.derivative.hasDerivAt (1-y)).comp y hi
  exact (hd.const_mul _).continuousAt.continuousWithinAt

theorem hasDerivAt_phi {q h y : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) (hy : y ∈ Ioo 0 2) :
    HasDerivAt (phi q h) (phiD q h y) y :=
  hasDerivAt_tsum_of_isPreconnected (g := fun k z => phiMode q h z (k+1))
    (g' := fun k z => phiModeD q h z (k+1)) (summable_major hq hQ) isOpen_Ioo isPreconnected_Ioo
    (fun k z _ => hasDerivAt_phiMode q h z (k+1))
    (fun k _ hz => modeD_major hq (Ioo_subset_Icc_self hz) k)
    (show (1:ℝ) ∈ Ioo 0 2 by constructor <;> norm_num)
    (Summable.of_norm_bounded (summable_major hq hQ)
      (fun k => mode_major hq (show (1:ℝ) ∈ Icc 0 2 by constructor <;> norm_num) k)) hy

theorem hasDerivAt_phiD {q h y : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) (hy : y ∈ Ioo 0 2) :
    HasDerivAt (phiD q h) (phiDD q h y) y :=
  hasDerivAt_tsum_of_isPreconnected (g := fun k z => phiModeD q h z (k+1))
    (g' := fun k z => phiModeDD q h z (k+1)) (summable_major hq hQ) isOpen_Ioo isPreconnected_Ioo
    (fun k z _ => hasDerivAt_phiModeD q h z (k+1))
    (fun k _ hz => modeDD_major hq (Ioo_subset_Icc_self hz) k)
    (show (1:ℝ) ∈ Ioo 0 2 by constructor <;> norm_num)
    (Summable.of_norm_bounded (summable_major hq hQ)
      (fun k => modeD_major hq (show (1:ℝ) ∈ Icc 0 2 by constructor <;> norm_num) k)) hy

theorem strictMonoOn_phi_small {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (h0 : 0 ≤ h) (h8 : h ≤ 1/8) : StrictMonoOn (phi q h) (Icc 0 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_phi hq hQ)
  rw [interior_Icc]
  intro y hy
  rw [(hasDerivAt_phi hq hQ hy).deriv]
  exact phiD_pos_small_floor hq hQ h0 h8 (Ioo_subset_Icc_self hy)

theorem strictMonoOn_phiD_large {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) : StrictMonoOn (phiD q h) (Icc 0 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_phiD hq.le hQ)
  rw [interior_Icc]
  intro y hy
  rw [(hasDerivAt_phiD hq.le hQ hy).deriv]
  exact phiDD_pos_large_floor hq hQ h8 h6 (Ioo_subset_Icc_self hy)

theorem strictConvexOn_phi_large {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) : StrictConvexOn ℝ (Icc 0 2) (phi q h) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) (continuousOn_phi hq.le hQ)
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [(hasDerivAt_phi hq.le hQ hx).deriv,(hasDerivAt_phi hq.le hQ hy).deriv]
  exact strictMonoOn_phiD_large hq hQ h8 h6 (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

end GaussianChains.PackedFace



