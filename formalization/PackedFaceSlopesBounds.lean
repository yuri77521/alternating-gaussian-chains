import PackedFaceSlopes
import PackedFaceBoundsChebyshev
import PackedFaceBounds
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The 39 and 9 constants in the slope proof are obtained from bounds for
the actual differentiated Chebyshev summands. -/

noncomputable section
namespace GaussianChains.PackedFace
open Polynomial.Chebyshev

private theorem abs_A_le_three (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |2*modeT n x-1| ≤ 3 := by
  have ht := abs_le.mp (abs_eval_T (n:ℤ) hx)
  unfold modeT
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

private theorem abs_prefactor (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    |(-1:ℝ)^(n+1)*n*q^(n^2-1)| = (n:ℝ)*q^(n^2-1) := by
  simp [abs_mul, abs_pow, abs_of_nonneg hq]

theorem endpointMode_bound (n : ℕ) {q x z : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |endpointMode n q x z| ≤ 9 * weightedMode q 2 n := by
  have hu : |modeU n z| ≤ (n : ℝ) := abs_eval_U_pred n hz
  rw [endpointMode, abs_mul, abs_mul, abs_prefactor n hq, abs_pow]
  calc
    _ ≤ (n:ℝ)*q^(n^2-1)*(3:ℝ)^2*n := by
      gcongr
      exact abs_A_le_three n hx
    _ = _ := by unfold weightedMode; ring

theorem endpointDx_bound {n : ℕ} (hn : 1 ≤ n) {q x z dz : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) (hd : |dz| ≤ 3) :
    |endpointDx n q x z dz| ≤ 39 * weightedMode q 4 n := by
  have hA := abs_A_le_three n hx
  have ht := abs_eval_derivative_T n hx
  have hu : |modeU n z| ≤ (n : ℝ) := abs_eval_U_pred n hz
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : ((n:ℝ)-1)^2 ≤ (n:ℝ)^2 := by nlinarith
  have hv : |(U ℝ ((n:ℤ)-1)).derivative.eval z| ≤ (n:ℝ)^3 := calc
    _ ≤ _ := abs_eval_derivative_U_pred n hz
    _ ≤ (n:ℝ)*((n:ℝ)^2) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by ring
  rw [endpointDx, abs_mul, abs_prefactor n hq]
  calc
    _ ≤ (n:ℝ)*q^(n^2-1) * (|4*(2*modeT n x-1)*(T ℝ n).derivative.eval x*modeU n z| +
        |(2*modeT n x-1)^2*(U ℝ ((n:ℤ)-1)).derivative.eval z*dz|) := by
      gcongr; exact abs_add_le _ _
    _ ≤ (n:ℝ)*q^(n^2-1) * (4*3*(n:ℝ)^2*n+3^2*(n:ℝ)^3*3) := by
      simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ)<4)]
      gcongr
    _ = _ := by unfold weightedMode; ring

theorem endpointDq_scaled_bound {n : ℕ} (hn : 2 ≤ n) {q x z : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |q * endpointDq n q x z| ≤ 9 * weightedMode q 4 n := by
  have he : ((n^2-1 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast Nat.sub_le (n^2) 1
  rw [endpointMode_scaled_q hn, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (n:ℝ)^2 * (9 * weightedMode q 2 n) :=
      mul_le_mul he (endpointMode_bound n hq hx hz) (abs_nonneg _) (sq_nonneg _)
    _ = _ := by unfold weightedMode; ring

/-- Generic consequence of the fourth Gaussian majorant for real-valued
tails dominated term by term, including absolute convergence. -/
theorem endpoint_tail_control {f : ℕ → ℝ} {C q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (h : ∀ k, |f k| ≤ C * weightedMode q 4 (k+3)) (hC : 0 ≤ C) :
    Summable f ∧ |∑' k, f k| ≤ C*(q^3*tailH) := by
  obtain ⟨hm,ht⟩ := fourth_tail_bound hq hQ
  have hh : ∀ k, ‖f k‖ ≤ C * weightedMode q 4 (k+3) := by
    simpa only [Real.norm_eq_abs] using h
  have hm' := hm.hasSum.mul_left C
  have hb := tsum_of_norm_bounded hm' hh
  rw [Real.norm_eq_abs] at hb
  exact ⟨Summable.of_norm_bounded hm'.summable hh, hb.trans (mul_le_mul_of_nonneg_left ht hC)⟩

theorem endpointDx_tail {q x z dz : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) (hd : |dz| ≤ 3) :
    Summable (fun k : ℕ => endpointDx (k+3) q x z dz) ∧
      |∑' k : ℕ, endpointDx (k+3) q x z dz| ≤ 39*(q^3*tailH) :=
  endpoint_tail_control hq hQ (fun k => endpointDx_bound (by omega) hq hx hz hd) (by norm_num)

theorem endpointDq_scaled_tail {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    Summable (fun k : ℕ => q*endpointDq (k+3) q x z) ∧
      |∑' k : ℕ, q*endpointDq (k+3) q x z| ≤ 9*(q^3*tailH) :=
  endpoint_tail_control hq hQ (fun k => endpointDq_scaled_bound (by omega) hq hx hz) (by norm_num)

end GaussianChains.PackedFace
