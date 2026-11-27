import PackedFaceSeries
import PackedFaceBounds
import PackedFaceBoundsChebyshev
import PackedFaceBoundsEndpoints
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Strict signs of the differentiated energy series on the closed squared-displacement interval. -/

namespace GaussianChains.PackedFace

open Polynomial Polynomial.Chebyshev Real

theorem modeD_bound {q h y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Set.Icc 0 2)
    (n : ℕ) :
    |phiModeD q h y n| ≤ amplitude h n ^ 2 * weightedMode q 2 n := by
  have hd := abs_eval_derivative_T n (show 1-y ∈ Set.Icc (-1) 1 by
    constructor <;> linarith [hy.1,hy.2])
  simp only [phiModeD, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hq, sq_abs, weightedMode]
  calc
    _ ≤ (q^(n^2-1) * amplitude h n ^ 2) * (n : ℝ)^2 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

theorem modeDD_bound {q h y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Set.Icc 0 2)
    (n : ℕ) : |phiModeDD q h y n| ≤ 9 * weightedMode q 4 n := by
  have hd := abs_eval_derivative_derivative_T n (show 1-y ∈ Set.Icc (-1) 1 by
    constructor <;> linarith [hy.1,hy.2])
  have ha : amplitude h n ^ 2 ≤ (3:ℝ)^2 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) (abs_amplitude_le h n) 2
  simp only [phiModeDD, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hq, sq_abs, weightedMode]
  calc
    _ ≤ (q^(n^2-1) * (3:ℝ)^2) * (n : ℝ)^4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left ha (pow_nonneg hq _)) hd (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem tail_control {f g : ℕ → ℝ} {C B : ℝ} (hC : 0 ≤ C)
    (hg : Summable g) (hB : (∑' n, g n) ≤ B) (h : ∀ n, |f n| ≤ C * g n) :
    Summable f ∧ -(C * B) ≤ ∑' n, f n := by
  have hm : ∀ n, ‖f n‖ ≤ C * g n := by simpa only [Real.norm_eq_abs] using h
  have hsum := hg.hasSum.mul_left C
  have hb := tsum_of_norm_bounded hsum hm
  rw [Real.norm_eq_abs] at hb
  exact ⟨Summable.of_norm_bounded hsum.summable hm,
    (neg_le_neg (mul_le_mul_of_nonneg_left hB hC)).trans (abs_le.mp hb).1⟩

private theorem amplitudes_low (h : ℝ) :
    amplitude h 1 = 2*cos (2*π*h)-1 ∧
    amplitude h 2 = 4*cos (2*π*h)^2-3 ∧
    amplitude h 3 = 8*cos (2*π*h)^3-6*cos (2*π*h)-1 := by
  have h₃ : T ℝ 3 = 2 * X * T ℝ 2 - T ℝ 1 := T_add_two ℝ 1
  refine ⟨?_, ?_, ?_⟩ <;> simp [amplitude,h₃,T_two] <;> ring

private theorem modeD_one (q h y : ℝ) : phiModeD q h y 1 = amplitude h 1 ^ 2 := by
  simp [phiModeD]

private theorem modeDD_one_two (q h y : ℝ) :
    phiModeDD q h y 1 = 0 ∧ phiModeDD q h y 2 = 4 * q^3 * amplitude h 2 ^ 2 := by
  norm_num [phiModeDD,T_two,derivative_mul,derivative_pow] <;> ring

theorem phiD_pos_small_floor {q h y : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ faceQ)
    (h0 : 0 ≤ h) (h8 : h ≤ 1/8) (hy : y ∈ Set.Icc 0 2) : 0 < phiD q h y := by
  obtain ⟨ha₁,ha₂,ha₃⟩ := small_floor_modes (cos_floor_small h0 h8) (cos_le_one _)
  obtain ⟨a1,a2,a3⟩ := amplitudes_low h
  rw [← a1] at ha₁
  rw [← a2] at ha₂
  rw [← a3] at ha₃
  have s2 := modeD_bound (h := h) hq hy 2
  have s3 := modeD_bound (h := h) hq hy 3
  have e2 : amplitude h 2 ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) ha₂ 2
  have hp3 := pow_le_pow_left₀ hq hqQ 3
  have hp8 := pow_le_pow_left₀ hq hqQ 8
  norm_num [weightedMode] at s2 s3
  have l2 : -(4*faceQ^3) ≤ phiModeD q h y 2 := by
    have hb := mul_le_mul e2 hp3 (pow_nonneg hq 3) zero_le_one
    nlinarith only [hb,(abs_le.mp s2).1]
  have l3 : -(54*faceQ^8) ≤ phiModeD q h y 3 := by
    have hb := mul_le_mul ha₃.le hp8 (pow_nonneg hq 8) (by norm_num : (0:ℝ) ≤ 6)
    nlinarith only [hb,(abs_le.mp s3).1]
  obtain ⟨hs,hb⟩ := second_tail_bound hq hqQ
  have hpoint (n : ℕ) : |phiModeD q h y (n+4)| ≤ 9 * weightedMode q 2 (n+4) := by
    refine (modeD_bound hq hy (n+4)).trans (mul_le_mul_of_nonneg_right ?_ (weightedMode_nonneg hq _ _))
    have ha := pow_le_pow_left₀ (abs_nonneg _) (abs_amplitude_le h (n+4)) 2
    norm_num at ha
    simpa using ha
  obtain ⟨ht,hl⟩ := tail_control (by norm_num : (0:ℝ) ≤ 9) hs hb hpoint
  let f := fun k : ℕ => phiModeD q h y (k+1)
  have hf : Summable f := (summable_nat_add_iff 3).mp ht
  have eq := hf.sum_add_tsum_nat_add 3
  change _ + (∑' n : ℕ, phiModeD q h y (n+4)) = phiD q h y at eq
  simp [f,Finset.sum_range_succ,modeD_one] at eq
  rw [show 9 * (16 * faceQ^15 / (1-tailRatio faceQ 2 4)) =
    144*faceQ^15/(1-tailRatio faceQ 2 4) by ring] at hl
  linarith only [face_constant_bounds.1, ha₁, l2, l3, hl, eq]

theorem phiDD_pos_large_floor {q h y : ℝ} (hq : 0 < q) (hqQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) (hy : y ∈ Set.Icc 0 2) : 0 < phiDD q h y := by
  obtain ⟨hcos,hcos'⟩ := cos_floor_large h8 h6
  have ha := (large_floor_modes hcos hcos').1
  rw [← (amplitudes_low h).2.1] at ha
  obtain ⟨hs,hb⟩ := fourth_tail_bound hq.le hqQ
  obtain ⟨ht,hl⟩ := tail_control (by norm_num : (0:ℝ) ≤ 9) hs hb
    (fun n => modeDD_bound (h := h) hq.le hy (n+3))
  let f := fun k : ℕ => phiModeDD q h y (k+1)
  have hf : Summable f := (summable_nat_add_iff 2).mp ht
  have eq := hf.sum_add_tsum_nat_add 2
  change _ + (∑' n : ℕ, phiModeDD q h y (n+3)) = phiDD q h y at eq
  obtain ⟨e1,e2⟩ := modeDD_one_two q h y
  simp [f,Finset.sum_range_succ,e1,e2] at eq
  have ha' := mul_le_mul_of_nonneg_left ha (pow_nonneg hq.le 3)
  have hpositive := mul_pos (pow_pos hq 3) face_constant_bounds.2.1
  nlinarith only [ha',hpositive,hl,eq]

end GaussianChains.PackedFace
