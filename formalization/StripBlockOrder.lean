import StripSupports
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Circle-order obstruction for the block types in the small-floor proof.
A decrease in the sequence of peak quadrants costs one full turn of the chosen
integer lift. The cyclic ordered block midpoints have only one such turn. -/
namespace GaussianChains.Strip
open Real

def descents (p : ℕ → ℕ) (K : ℕ) : ℤ :=
  ∑ i ∈ Finset.range K, if p (i+1) < p i then 1 else 0

theorem peak_one_turn {K : ℕ} {d : ℝ} (hd : 2*d < π/2) (p : ℕ → ℕ)
    (t : ℕ → ℤ) (u : ℕ → ℝ) (hp : ∀ i ≤ K, p i < 4)
    (ht : t K = t 0+1) (hord : ∀ i < K, u i ≤ u (i+1))
    (hnear : ∀ i ≤ K, |u i-((p i:ℝ)+4*(t i:ℝ))*(π/2)| ≤ d) :
    descents p K ≤ 1 := by
  have hf (i : ℕ) (hi : i < K) : (p i:ℤ)+4*t i ≤ (p (i+1):ℤ)+4*t (i+1) := by
    by_contra! hn
    have hint : (p (i+1):ℤ)+4*t (i+1)+1 ≤ (p i:ℤ)+4*t i := by omega
    have hreal : (p (i+1):ℝ)+4*(t (i+1):ℝ)+1 ≤ (p i:ℝ)+4*(t i:ℝ) := by exact_mod_cast hint
    have hu := (abs_le.mp (hnear i hi.le)).1
    have hv := (abs_le.mp (hnear (i+1) hi)).2
    nlinarith only [hu,hv,hord i hi,hd,
      mul_le_mul_of_nonneg_right hreal (by positivity : 0 ≤ π/2)]
  have hdiff (i : ℕ) (hi : i < K) :
      (if p (i+1)<p i then (1:ℤ) else 0) ≤ t (i+1)-t i := by
    have h := hf i hi
    have hp₁ := hp i hi.le
    have hp₂ := hp (i+1) hi
    split_ifs <;> omega
  have h := Finset.sum_le_sum (s:=Finset.range K) fun i hi =>
    hdiff i (Finset.mem_range.mp hi)
  rw [Finset.sum_range_sub,ht] at h
  simpa only [add_sub_cancel_left,descents] using h

def boundaries (A : Support) : List ℕ :=
  ((List.finRange 5).filter (· ∈ A)).map (fun i => i.val+1)

def blocks (A : Support) : List ℕ :=
  List.zipWith (fun a b => b-a) (0::boundaries A) (boundaries A++[6])

def peakList (A : Support) : List ℕ :=
  List.zipWith (fun i b => 2*(i%2)+(if b%2=0 then 1 else 0)) (0::boundaries A) (blocks A)

def peakIndex (A : Support) (i : ℕ) : ℕ :=
  ((peakList A)[i%(peakList A).length]?).getD 0

/-- Exhaustive circle-order result with no continuous variables discretized.
All subdivisions of six sites that include a distinguished wrapping slack gap
are allowed as inputs. -/
theorem allowed_blocks_of_peak_order : ∀ A : Support,
    descents (peakIndex A) (peakList A).length ≤ 1 →
      blocks A ∈ [[6],[1,5],[2,4],[3,3],[4,2],[5,1],[2,2,2]] := by decide

/-- For three or more arcs, any mixture involving an odd block is impossible. -/
theorem many_blocks_are_dimers : ∀ A : Support,
    descents (peakIndex A) (peakList A).length ≤ 1 →
    3 ≤ (blocks A).length → blocks A = [2,2,2] := by decide

end GaussianChains.Strip
