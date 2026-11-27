import ChainGeometry
import ChainEnergy
import ClustersMoments

noncomputable section

open Finset AlternatingMoments

namespace GaussianChains.OddBlock

/-- Angular offsets, with an arbitrary choice of origin. A block may cross
the cut of the labelled unit cell. -/
def offset {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (start : ℕ) (origin : ℝ) (i : ℕ) : ℝ :=
  2*Real.pi*liftSite hN x (start+i) - origin

theorem offset_gap {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (start : ℕ) (origin : ℝ) (i : ℕ) :
    offset hN x start origin (i+1) - offset hN x start origin i =
      2*Real.pi*gap hN x ⟨(start+i)%N, Nat.mod_lt _ hN⟩ := by
  rw [← gap_lift_period]
  simp only [offset, Nat.add_assoc]
  ring

/-- Resetting the first block sign to +1 multiplies each global charge by
the same sign. Even period keeps this true across the last gap. -/
theorem block_charge (m : ℕ) (hm : 0 < 2*m) (start i : ℕ) :
    charge (N := 2*m) ⟨(start+i)%(2*m), Nat.mod_lt _ hm⟩ =
      (-1:ℝ)^start * (-1:ℝ)^i := by
  change (-1:ℝ)^((start+i)%(2*m)) = _
  rw [← pow_add]
  calc
    _ = (-1:ℝ)^((start+i)%(2*m) + (2*m)*((start+i)/(2*m))) := by
      simp [pow_add, pow_mul]
    _ = _ := by rw [Nat.mod_add_div]

private theorem alternating_mass (n : ℕ) : ∑ i ∈ range n, (-1:ℝ)^i =
    (if n%2=1 then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have e : Even n := Nat.even_iff.mpr h
      simp [h, e.neg_one_pow, show (n+1)%2=1 by omega]
    · have e : Odd n := Nat.odd_iff.mpr h
      simp [h, e.neg_one_pow, show (n+1)%2=0 by omega]

/-- A nonzero net jump in a cluster forces an odd number of sites. Its
signed charge then equals its first charge, including blocks crossing the cut. -/
theorem block_mass (m : ℕ) (hm : 0 < 2*m) (start n : ℕ) :
    (∑ i ∈ range n, charge (N := 2*m) ⟨(start+i)%(2*m), Nat.mod_lt _ hm⟩) =
      if n%2=1 then (-1:ℝ)^start else 0 := by
  simp_rw [block_charge m hm, ← mul_sum, alternating_mass]
  split_ifs <;> simp

theorem odd_of_net_jump {m : ℕ} (hm : 0 < 2*m) (start n : ℕ)
    (hnet : (∑ i ∈ range n, charge (N := 2*m) ⟨(start+i)%(2*m), Nat.mod_lt _ hm⟩) ≠ 0) :
    ∃ j, n=2*j+1 := by
  rw [block_mass m hm start n] at hnet
  split_ifs at hnet with h
  · exact ⟨n/2, by omega⟩
  · contradiction

/-- Both alternating gap arrays are consecutive angular gaps of the same
labelled physical cell. -/
theorem block_gaps {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (start : ℕ)
    (origin : ℝ) (r : ℕ) :
    let u := offset hN x start origin
    gapA u r = 2*Real.pi*gap hN x ⟨(start+2*r)%N, Nat.mod_lt _ hN⟩ ∧
    gapB u r = 2*Real.pi*gap hN x ⟨(start+(2*r+1))%N, Nat.mod_lt _ hN⟩ :=
  ⟨offset_gap hN x start origin (2*r), offset_gap hN x start origin (2*r+1)⟩

/-- The two moment identities and the lower bound of (4), for an actual
contiguous odd block. The floor in `Feasible` is measured in periods. -/
theorem feasible_block_moments {N : ℕ} {hN : 0 < N} {h : ℝ} {x : Fin N → ℝ}
    (hh : 0 ≤ h) (hx : Feasible hN h x) (start j : ℕ) (origin : ℝ) :
    let u := offset hN x start origin
    altSum u j = u 0 + ∑ r ∈ range j, gapB u r ∧
    altSum (fun i => u i^2) j - (altSum u j)^2 =
      gapVariance j (gapA u) (gapB u) ∧
    (j : ℝ)*((j : ℝ)+1)*(2*Real.pi*h)^2 ≤ altSum (fun i => u i^2) j - (altSum u j)^2 := by
  dsimp only
  refine ⟨firstMoment _ _, secondMoment _ _, variance_lower _ _ (by positivity) ?_⟩
  intro i _
  rw [offset_gap]
  exact mul_le_mul_of_nonneg_left (hx _) (by positivity)

/-- For three actual sites, fixing their first signed moment gives precisely
the `tripleVariance` coordinates used by the archived derivative theorem. -/
theorem feasible_triple {N : ℕ} {hN : 0 < N} {h : ℝ} {x : Fin N → ℝ}
    (hx : Feasible hN h x) (start : ℕ) (origin : ℝ) :
    let u := offset hN x start origin
    let p := altSum u 1
    let a := gapA u 0
    let b := gapB u 0
    (u 0 = p-b ∧ u 1 = p-b+a ∧ u 2 = p+a) ∧
    tripleVariance p a b = 2*a*b ∧
    HasDerivAt (fun t => tripleVariance p t b) (2*b) a ∧
    HasDerivAt (fun t => tripleVariance p a t) (2*a) b ∧
    2*(2*Real.pi*h) ≤ 2*b ∧ 2*(2*Real.pi*h) ≤ 2*a := by
  let u := offset hN x start origin
  have h1 : altSum u 1 = u 0 + gapB u 0 := by simp [firstMoment]
  have ha : 2*Real.pi*h ≤ gapA u 0 := by
    rw [(block_gaps hN x start origin 0).1]
    exact mul_le_mul_of_nonneg_left (hx _) (by positivity)
  have hb : 2*Real.pi*h ≤ gapB u 0 := by
    rw [(block_gaps hN x start origin 0).2]
    exact mul_le_mul_of_nonneg_left (hx _) (by positivity)
  dsimp only
  refine ⟨?_, tripleVariance_eq _ _ _, triple_gap_derivatives (altSum u 1) _ _ _ ha hb⟩
  change u 0 = _ ∧ u 1 = _ ∧ u 2 = _
  change u 0 = altSum u 1 - (u 2 - u 1) ∧
    u 1 = altSum u 1 - (u 2 - u 1) + (u 1 - u 0) ∧
    u 2 = altSum u 1 + (u 1 - u 0)
  change altSum u 1 = u 0 + (u 2 - u 1) at h1
  exact ⟨by linarith, by linarith, by linarith⟩

end GaussianChains.OddBlock
