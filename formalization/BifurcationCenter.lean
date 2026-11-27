import BifurcationSlope

noncomputable section
namespace GaussianChains.Bifurcation

def oddMode (k : ℕ) := 2*k+1

def oddSlopeTerm (q z : ℝ) (k : ℕ) : ℝ :=
  let n := oddMode k
  (n:ℝ) * q^(n^2) * slopeFactor (n*z)

private theorem oddSlopeTerm_norm (q z : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/2) (k : ℕ) :
    ‖oddSlopeTerm q z (k+1)‖ ≤ (27/256*q*|slopeFactor z|) * (1/2:ℝ)^k := by
  let n := oddMode (k+1)
  have hn : n = 2*k+3 := by dsimp [n, oddMode]; omega
  change ‖(n:ℝ)*q^(n^2)*slopeFactor (n*z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)*q^(n^2))]
  calc
    _ ≤ ((n:ℝ)*q^(n^2)) * ((n:ℝ)^2 * |slopeFactor z|) :=
      mul_le_mul_of_nonneg_left (slopeFactor_odd_bound (k+1) z) (by positivity)
    _ = ((n:ℝ)^3 * q^(n^2)) * |slopeFactor z| := by ring
    _ ≤ (27/256*q*(1/2:ℝ)^k) * |slopeFactor z| := by
      rw [hn]
      exact mul_le_mul_of_nonneg_right (odd_weight_tail k hq hq') (abs_nonneg _)
    _ = _ := by ring

theorem centered_slope_lower {q z : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/2)
    (hF : 0 ≤ slopeFactor z) :
    (1-54/256)*q*slopeFactor z ≤ ∑' k, oddSlopeTerm q z k := by
  let c := 27/256*q*|slopeFactor z|
  have hg := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hdom : Summable (fun k : ℕ => c * (1/2:ℝ)^k) := hg.mul_left c
  have ht : Summable (fun k : ℕ => oddSlopeTerm q z (k+1)) :=
    Summable.of_norm_bounded hdom (oddSlopeTerm_norm q z hq hq')
  have hs : Summable (oddSlopeTerm q z) := (summable_nat_add_iff 1).mp ht
  have htn : Summable (fun k : ℕ => ‖oddSlopeTerm q z (k+1)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (oddSlopeTerm_norm q z hq hq') hdom
  have h := (norm_tsum_le_tsum_norm htn).trans
    (htn.tsum_le_tsum (oddSlopeTerm_norm q z hq hq') hdom)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num),
    Real.norm_eq_abs] at h
  have hn := (abs_le.mp h).1
  change -(27/256*q*|slopeFactor z| * (1-1/2)⁻¹) ≤ _ at hn
  rw [abs_of_nonneg hF] at hn
  rw [← hs.sum_add_tsum_nat_add 1]
  have first : oddSlopeTerm q z 0 = q*slopeFactor z := by simp [oddSlopeTerm,oddMode]
  simp only [Finset.sum_range_one, first]
  linarith

/-- The centered energy from (2), after the even modes vanish and the two
opposite odd triple amplitudes add. -/
def centeredFourier (q c h : ℝ) : ℝ :=
  1 - (4*c/3) * ∑' k, q^((oddMode k)^2) * (2*Real.cos (oddMode k*(2*Real.pi*h))-1)^2

private theorem slopeFactor_abs_le (z : ℝ) : |slopeFactor z| ≤ 3 := by
  unfold slopeFactor
  rw [abs_mul]
  calc
    _ ≤ 3 * 1 := mul_le_mul (abs_le.mpr ⟨by linarith [Real.neg_one_le_cos z],
        by linarith [Real.cos_le_one z]⟩)
      (abs_le.mpr ⟨Real.neg_one_le_sin z, Real.sin_le_one z⟩)
      (abs_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem centeredFourier_hasDerivAt {q c : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (h : ℝ) :
    HasDerivAt (centeredFourier q c)
      ((32*Real.pi*c/3) * ∑' k, oddSlopeTerm q (2*Real.pi*h) k) h := by
  let g := fun k (y:ℝ) => q^((oddMode k)^2) * (2*Real.cos (oddMode k*(2*Real.pi*y))-1)^2
  let dg := fun k (y:ℝ) => -8*Real.pi * oddSlopeTerm q (2*Real.pi*y) k
  have hd (k : ℕ) (y : ℝ) : HasDerivAt (g k) (dg k y) y := by
    have hangle := ((hasDerivAt_id' y).const_mul (2*Real.pi)).const_mul (oddMode k:ℝ)
    have hc := (((hangle.cos.const_mul 2).sub_const 1).pow 2).const_mul (q ^ (oddMode k)^2)
    convert hc using 1
    dsimp [dg, oddSlopeTerm, slopeFactor]
    ring
  have hratio : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have hg := summable_geometric_of_lt_one hq hq'
  have hpoly : Summable (fun k : ℕ => (k:ℝ)*q^k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hratio
  have hdom : Summable (fun k : ℕ => (24*Real.pi)*((2*(k:ℝ)+1)*q^k)) := by
    convert ((hpoly.mul_left 2).add hg).mul_left (24*Real.pi) using 1
    ext k; ring
  have hexp (k : ℕ) : q^(oddMode k ^ 2) ≤ q^k := by
    apply pow_le_pow_of_le_one hq hq'.le
    dsimp [oddMode]
    nlinarith [Nat.zero_le (k^2)]
  have hbd (k : ℕ) (y : ℝ) :
      ‖dg k y‖ ≤ (24*Real.pi)*((2*(k:ℝ)+1)*q^k) := by
    dsimp [dg, oddSlopeTerm]
    simp only [abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (oddMode k)),
      abs_of_nonneg (pow_nonneg hq _)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 8)]
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left (hexp k) (Nat.cast_nonneg (oddMode k)))
      (slopeFactor_abs_le (oddMode k*(2*Real.pi*y))) (abs_nonneg _) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 8*Real.pi by positivity)
    dsimp [oddMode] at hh ⊢
    push_cast at hh ⊢
    linarith
  have hz : Summable (fun k : ℕ => g k 0) := by
    apply Summable.of_nonneg_of_le (fun k => by dsimp [g]; positivity) _ hg
    intro k
    simpa [g,show (2:ℝ)-1 = 1 by norm_num] using hexp k
  have hs := hasDerivAt_tsum hdom hd hbd hz h
  have he := (hasDerivAt_const h (1:ℝ)).sub (hs.const_mul (4*c/3))
  convert he using 1
  dsimp [dg]
  rw [tsum_mul_left]
  ring

theorem slopeFactor_pos_of_floor {h : ℝ} (h₀ : 0 < h) (h₁ : h < 1/6) :
    0 < slopeFactor (2*Real.pi*h) := by
  have hz : 0 < 2*Real.pi*h := by positivity
  have hπ : 2*Real.pi*h < Real.pi/3 := by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr h₁)]
  have hcos := Real.strictAntiOn_cos ⟨hz.le, by linarith [Real.pi_pos]⟩
    (b := Real.pi/3) ⟨by positivity, by linarith [Real.pi_pos]⟩ hπ
  rw [Real.cos_pi_div_three] at hcos
  exact mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi hz (by linarith [Real.pi_pos]))

/-- The centered packed-triple branch has a positive inward slope on the whole open
floor interval. The proof uses strict positivity of the combined odd-mode series. -/
theorem centeredFourier_deriv_pos {q c h : ℝ} (hq : 0 < q) (hq' : q ≤ 1/2) (hc : 0 < c)
    (h₀ : 0 < h) (h₁ : h < 1/6) : 0 < deriv (centeredFourier q c) h := by
  rw [(centeredFourier_hasDerivAt hq.le (by linarith) h).deriv]
  have hF := slopeFactor_pos_of_floor h₀ h₁
  have hs := centered_slope_lower hq.le hq' hF.le
  exact mul_pos (by positivity) (lt_of_lt_of_le (by positivity) hs)

end GaussianChains.Bifurcation
