import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform real majorants for the differentiated Gaussian series on the packed face. -/

namespace GaussianChains.PackedFace

noncomputable section

def faceQ : ℝ := 17 / 50

/-- The polynomially weighted Gaussian mode in Eq. (9). -/
def weightedMode (q : ℝ) (p n : ℕ) : ℝ :=
  (n : ℝ) ^ p * q ^ (n ^ 2 - 1)

/-- Common ratio of the geometric majorant starting at the first omitted mode M. -/
def tailRatio (Q : ℝ) (p M : ℕ) : ℝ :=
  (((M : ℝ) + 1) / M) ^ p * Q ^ (2 * M + 1)

theorem weightedMode_nonneg {q : ℝ} (hq : 0 ≤ q) (p n : ℕ) : 0 ≤ weightedMode q p n := by
  unfold weightedMode
  positivity

private theorem weightedMode_step {q Q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (p M n : ℕ) (hM : 0 < M) (hn : M ≤ n) :
    weightedMode q p (n + 1) ≤ tailRatio Q p M * weightedMode q p n := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hn' : (M : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly : (n : ℝ) + 1 ≤ (((M : ℝ) + 1) / M) * n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hM']
    nlinarith only [hn']
  have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity) hpoly p
  have hexp : (n ^ 2 - 1) + (2 * M + 1) ≤ (n + 1) ^ 2 - 1 := by
    have hnsq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hnsq' : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e : (n + 1) ^ 2 = n ^ 2 + 2*n + 1 := by ring
    omega
  have hgauss := pow_le_pow_of_le_one hq (hqQ.trans hQ) hexp
  rw [pow_add] at hgauss
  have hqpow := pow_le_pow_left₀ hq hqQ (2*M+1)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  unfold weightedMode tailRatio
  rw [hcast]
  calc
    _ ≤ ((((M : ℝ) + 1) / M) * n) ^ p * (q ^ (n ^ 2 - 1) * q ^ (2*M+1)) :=
      mul_le_mul hpow hgauss (pow_nonneg hq _) (by positivity)
    _ ≤ ((((M : ℝ) + 1) / M) * n) ^ p * (q ^ (n ^ 2 - 1) * Q ^ (2*M+1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqpow (pow_nonneg hq _)) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem weightedMode_geometric {q Q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (p M : ℕ) (hM : 0 < M) (n : ℕ) :
    weightedMode q p (n + M) ≤ weightedMode q p M * tailRatio Q p M ^ n := by
  have hQ₀ : 0 ≤ Q := hq.trans hqQ
  have hr : 0 ≤ tailRatio Q p M := by unfold tailRatio; positivity
  have h := le_geom (u := fun k => weightedMode q p (k + M)) hr n (fun k _ => by
    simpa only [Nat.add_right_comm k 1 M] using
      weightedMode_step hq hqQ hQ p M (k+M) hM (by omega))
  simpa only [Nat.zero_add, mul_comm (tailRatio Q p M ^ n)] using h

/-- Absolute convergence and the value bound use the same underlying pointwise majorant. -/
theorem weightedMode_tail {q Q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (p M : ℕ) (hM : 0 < M) (hr : tailRatio Q p M < 1) :
    Summable (fun n : ℕ => weightedMode q p (n + M)) ∧
      (∑' n : ℕ, weightedMode q p (n + M)) ≤ weightedMode q p M / (1 - tailRatio Q p M) := by
  have hQ₀ : 0 ≤ Q := hq.trans hqQ
  have hr₀ : 0 ≤ tailRatio Q p M := by unfold tailRatio; positivity
  have hs := (hasSum_geometric_of_lt_one hr₀ hr).mul_left (weightedMode q p M)
  have hb := weightedMode_geometric hq hqQ hQ p M hM
  have hs' := Summable.of_nonneg_of_le (fun n => weightedMode_nonneg hq p (n+M)) hb hs.summable
  refine ⟨hs', ?_⟩
  calc
    _ ≤ _ := hs'.tsum_le_tsum hb hs.summable
    _ = _ := by rw [hs.tsum_eq, div_eq_mul_inv]

def tailH : ℝ := 81 * faceQ ^ 5 / (1 - tailRatio faceQ 4 3)

theorem fourth_tail_bound {q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ faceQ) :
    Summable (fun n : ℕ => weightedMode q 4 (n+3)) ∧
      (∑' n : ℕ, weightedMode q 4 (n+3)) ≤ q^3 * tailH := by
  have hr : tailRatio faceQ 4 3 < 1 := by norm_num [tailRatio, faceQ]
  obtain ⟨hs,h⟩ := weightedMode_tail hq hqQ (by norm_num [faceQ]) 4 3 (by decide) hr
  refine ⟨hs, h.trans ?_⟩
  have hp := pow_le_pow_left₀ hq hqQ 5
  have hp' := mul_le_mul_of_nonneg_left hp (pow_nonneg hq 3)
  unfold weightedMode tailH
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right (sub_pos.mpr hr)]
  norm_num
  nlinarith only [hp']

theorem second_tail_bound {q : ℝ} (hq : 0 ≤ q) (hqQ : q ≤ faceQ) :
    Summable (fun n : ℕ => weightedMode q 2 (n+4)) ∧
      (∑' n : ℕ, weightedMode q 2 (n+4)) ≤ 16 * faceQ^15 / (1-tailRatio faceQ 2 4) := by
  have hr : tailRatio faceQ 2 4 < 1 := by norm_num [tailRatio, faceQ]
  obtain ⟨hs,h⟩ := weightedMode_tail hq hqQ (by norm_num [faceQ]) 2 4 (by decide) hr
  refine ⟨hs,h.trans ?_⟩
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hr)).mpr
  norm_num [weightedMode]
  exact pow_le_pow_left₀ hq hqQ 15

theorem face_constant_bounds :
    0 < 17/100 - 4*faceQ^3 - 54*faceQ^8 - 144*faceQ^15/(1-tailRatio faceQ 2 4) ∧
    0 < 4-9*tailH ∧ 39*tailH < 16 ∧ 9*tailH < 6 := by
  norm_num [tailH, tailRatio, faceQ]

end
end GaussianChains.PackedFace
