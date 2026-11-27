import CertTreeWidth

/-! Preserving strict trial comparisons and spatial cut tests under Appendix A's
constant shift and positive width-dependent rescaling of the pair kernel. -/
noncomputable section
namespace GaussianChains.WidthBounds

open FourierBounds

def coefficient (a s : ℝ) : ℝ := (scale a*nome a)/(scale s*nome s)

def offset (a s : ℝ) : ℝ := scale a - coefficient a s * scale s

theorem coefficient_pos {a s : ℝ} (ha : 0 < a) (hs : 0 < s) : 0 < coefficient a s := by
  have h₁ : 0 < scale a := Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)
  have h₂ : 0 < scale s := Real.sqrt_pos.mpr (div_pos Real.pi_pos hs)
  exact div_pos (mul_pos h₁ (nome_positive a)) (mul_pos h₂ (nome_positive s))

theorem matched_affine (a s x : ℝ) : matched a s x = coefficient a s * kernel s x + offset a s := by
  unfold matched offset coefficient
  ring

theorem matched_score {ι : Type*} (T : Finset ι) (w d : ι → ℝ) (a s : ℝ) :
    (∑ i ∈ T, w i * matched a s (d i)) =
      coefficient a s * (∑ i ∈ T, w i * kernel s (d i)) + offset a s * ∑ i ∈ T, w i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [matched_affine]
  ring

theorem matched_score_lt_iff {ι : Type*} (T : Finset ι) (w d₁ d₂ : ι → ℝ)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∑ i ∈ T, w i * matched a s (d₁ i)) < (∑ i ∈ T, w i * matched a s (d₂ i)) ↔
      (∑ i ∈ T, w i * kernel s (d₁ i)) < (∑ i ∈ T, w i * kernel s (d₂ i)) := by
  simp only [matched_score, add_lt_add_iff_right, mul_lt_mul_iff_right₀ (coefficient_pos ha hs)]

theorem matched_score_le_iff {ι : Type*} (T : Finset ι) (w d₁ d₂ : ι → ℝ)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∑ i ∈ T, w i * matched a s (d₁ i)) ≤ (∑ i ∈ T, w i * matched a s (d₂ i)) ↔
      (∑ i ∈ T, w i * kernel s (d₁ i)) ≤ (∑ i ∈ T, w i * kernel s (d₂ i)) := by
  simp only [matched_score, add_le_add_iff_right, mul_le_mul_iff_right₀ (coefficient_pos ha hs)]

/-- Every nonconstant derivative order scales by the same positive coefficient. -/
theorem matched_deriv_mul {a s : ℝ} (hs : 0 < s) (j : ℕ) (x : ℝ) :
    deriv^[j+1] (matched a s) x = coefficient a s * deriv^[j+1] (kernel s) x := by
  have hc : scale s ≠ 0 := (Real.sqrt_pos.mpr (div_pos Real.pi_pos hs)).ne'
  have hq := (nome_positive s).ne'
  rw [matched_derivative hs, kernel_deriv_series hs]
  simp only [Nat.succ_ne_zero, if_false, zero_add]
  unfold coefficient
  field_simp

theorem matched_cut_sum {ι : Type*} (T : Finset ι) (w d : ι → ℝ)
    {a s : ℝ} (hs : 0 < s) (j : ℕ) :
    (∑ i ∈ T, w i * deriv^[j+1] (matched a s) (d i)) =
      coefficient a s * ∑ i ∈ T, w i * deriv^[j+1] (kernel s) (d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [matched_deriv_mul hs]
  ring

/-- All successive spatial fields of the normalized kernel are genuine derivatives. -/
theorem matched_hasDerivAt {a s : ℝ} (hs : 0 < s) (j : ℕ) (x : ℝ) :
    HasDerivAt (deriv^[j] (matched a s)) (deriv^[j+1] (matched a s) x) x := by
  rw [matched_derivative hs, matched_derivative hs (j+1)]
  have hd := ((series_deriv (nome_positive s).le (nome_lt_one hs) j x).const_mul
    (2*FourierBounds.scale a*nome a*(2*Real.pi)^j)).const_add (if j=0 then FourierBounds.scale a else 0)
  simpa only [Nat.succ_ne_zero, if_false, zero_add, pow_succ, ← mul_assoc] using hd

end GaussianChains.WidthBounds
