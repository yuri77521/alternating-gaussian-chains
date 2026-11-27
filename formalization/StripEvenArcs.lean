import StripBlockOrder

/-! Geometric capacity of a single peak arc for the all-even alternatives.
The midpoint separation lower bounds use angular gaps. -/
namespace GaussianChains.Strip
open Real

/-- Localization at a common peak lifts each point into an interval of length
2d in the indicated turn. Two points in one turn cannot be farther apart. -/
private theorem same_turn_span {x y c d : ℝ} (hx : |x-c| ≤ d) (hy : |y-c| ≤ d) :
    y-x ≤ 2*d := by
  linarith only [(abs_le.mp hx).1,(abs_le.mp hy).2]

private theorem turn_gap {u v p d : ℝ} {k l : ℤ} (hd : d < π/2)
    (hx : |u-(p+2*π*(k:ℝ))| ≤ d) (hy : |v-(p+2*π*(l:ℝ))| ≤ d)
    (hord : u ≤ v) : k ≤ l := by
  by_contra! h
  have hk : (l:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (show l+1≤k by omega)
  nlinarith only [hord,hd,pi_pos,(abs_le.mp hx).1,(abs_le.mp hy).2,
    mul_le_mul_of_nonneg_left hk pi_pos.le]

private theorem shifted_peak {u p d : ℝ} {k : ℤ} (h : |u-(p+2*π*(k:ℝ))| ≤ d) :
    |(u+2*π)-(p+2*π*((k+1:ℤ):ℝ))| ≤ d := by
  convert h using 2 <;> push_cast <;> ring

/-- A 4+2 split would require two points in the common peak arc separated
by at least three gaps on *each* side. -/
theorem exclude_even_four_two {u v p d η : ℝ} {i j : ℤ} (hd : d < π/2)
    (hη : 2*d < 3*η) (hη₀ : 0 ≤ η)
    (h₁ : 3*η ≤ v-u) (h₂ : 3*η ≤ u+2*π-v)
    (hx : |u-(p+2*π*(i:ℝ))| ≤ d) (hy : |v-(p+2*π*(j:ℝ))| ≤ d) : False := by
  have hij := turn_gap hd hx hy (by linarith)
  have hji := turn_gap hd hy (shifted_peak hx) (by linarith)
  rcases (show j=i ∨ j=i+1 by omega) with h|h
  · rw [h] at hy; linarith [same_turn_span hx hy]
  · rw [h] at hy; linarith [same_turn_span hy (shifted_peak hx)]

/-- Among three dimers at least two consecutive midpoint separations must
fit inside the same arc, even if the chosen cut crosses that arc. -/
theorem exclude_even_three_dimers {u v w p d η : ℝ} {i j k : ℤ} (hd : d < π/2)
    (hη : 2*d < 4*η) (hη₀ : 0 ≤ η)
    (h₁ : 2*η ≤ v-u) (h₂ : 2*η ≤ w-v) (h₃ : 2*η ≤ u+2*π-w)
    (hx : |u-(p+2*π*(i:ℝ))| ≤ d) (hy : |v-(p+2*π*(j:ℝ))| ≤ d)
    (hz : |w-(p+2*π*(k:ℝ))| ≤ d) : False := by
  have hij := turn_gap hd hx hy (by linarith)
  have hjk := turn_gap hd hy hz (by linarith)
  have hki := turn_gap hd hz (shifted_peak hx) (by linarith)
  rcases (show (j=i ∧ k=i) ∨ (j=i ∧ k=i+1) ∨ (j=i+1 ∧ k=i+1) by omega) with h|h|h
  · rw [h.2] at hz; linarith [same_turn_span hx hz]
  · rw [h.1] at hy; rw [h.2] at hz; linarith [same_turn_span hz (shifted_peak hy)]
  · rw [h.1] at hy; linarith [same_turn_span hy (shifted_peak hx)]

end GaussianChains.Strip
