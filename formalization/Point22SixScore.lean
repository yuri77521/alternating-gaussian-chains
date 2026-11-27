import ChainScore
import Mathlib.Algebra.BigOperators.Fin

namespace GaussianChains.Point22

theorem sum_six (f : Fin 6 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ]
  ring

/-- The 15 unordered signed terms, with the signs fixed by their physical labels. -/
theorem six_score_terms (s : ℝ) (x : Fin 6 → ℝ) :
    pairScore s x =
    -kernel s (x 1-x 0) + kernel s (x 2-x 0) - kernel s (x 3-x 0) +
    kernel s (x 4-x 0) - kernel s (x 5-x 0) - kernel s (x 2-x 1) +
    kernel s (x 3-x 1) - kernel s (x 4-x 1) + kernel s (x 5-x 1) -
    kernel s (x 3-x 2) + kernel s (x 4-x 2) - kernel s (x 5-x 2) -
    kernel s (x 4-x 3) + kernel s (x 5-x 3) - kernel s (x 5-x 4) := by
  simp only [pairScore, sum_six]
  simp (config := {decide := true}) only [ite_true, ite_false]
  norm_num [charge]
  <;> ring

end GaussianChains.Point22
