import ArcOccupation
import Mathlib.Algebra.Order.ToIntervalMod

/-! Cutting the ordered cell at two points of opposite occupation selects
two contiguous odd blocks. Half-open arcs assign a jump at a cut to exactly
one of the blocks. -/

namespace GaussianChains.Occupation

open Finset Set

/-- Representative of an angular cut in the labelled cell, keeping the upper
endpoint when the angle agrees with the first site modulo the period. -/
noncomputable def cutRepresentative {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) (t : ℝ) :=
  toIocMod (show 0 < 2*Real.pi by positivity) (angle hN x 0) t

theorem mem_inCell_cutRepresentative {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) (t : ℝ) :
    cutRepresentative hN x t ∈ inCell hN x ↔ t ∈ circleSet hN x := by
  have hp : 0 < 2*Real.pi := by positivity
  have hmem := toIocMod_mem_Ioc hp (angle hN x 0) t
  have per : Function.Periodic (fun y => y ∈ circleSet hN x) (2*Real.pi) :=
    fun y => propext (circleSet_periodic hN x y)
  have pe := per.zsmul (toIocDiv hp (angle hN x 0) t) (cutRepresentative hN x t)
  change (toIocMod hp (angle hN x 0) t + _ ∈ circleSet hN x) = _ at pe
  rw [toIocMod_add_toIocDiv_zsmul] at pe
  rw [← inter_circleSet hx, mem_inter_iff, pe]
  exact and_iff_right hmem

theorem exists_cut (θ : ℕ → ℝ) (hθ : Monotone θ) (t : ℝ) (n : ℕ) :
    ∃ k ≤ n, ∀ i < n, θ i < t ↔ i < k := by
  induction n with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
    by_cases ht : θ n < t
    · refine ⟨n+1, le_rfl, ?_⟩
      intro i hi
      exact iff_of_true (lt_of_le_of_lt (hθ (by omega)) ht) hi
    · obtain ⟨k,hk,hc⟩ := ih
      refine ⟨k, by omega, ?_⟩
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact hc i hi
      · exact iff_of_false ht (by omega)

/-- At a cut with `k` sites strictly before it, the occupied arc test is
exactly the parity of `k`. Also valid at coincident labels. -/
theorem inCell_iff_cut_odd {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    {k : ℕ} (hk : k ≤ 2*m) {t : ℝ}
    (hc : ∀ i < 2*m, angle hN x i < t ↔ i < k) :
    t ∈ inCell hN x ↔ k%2=1 := by
  constructor
  · intro ht
    obtain ⟨r,hr,ht⟩ := mem_iUnion₂.mp ht
    have hrm := mem_range.mp hr
    have he := (hc (2*r) (by omega)).mp ht.1
    have ho : ¬2*r+1<k := fun h => (not_lt_of_ge ht.2) ((hc _ (by omega)).mpr h)
    omega
  · intro hk'
    let r := k/2
    have hr : r < m := by dsimp [r]; omega
    refine mem_iUnion₂.mpr ⟨r, mem_range.mpr hr, ?_⟩
    refine ⟨(hc (2*r) (by omega)).mpr (by dsimp [r]; omega), ?_⟩
    apply le_of_not_gt
    intro h
    have := (hc (2*r+1) (by omega)).mp h
    dsimp [r] at this
    omega

/-- Two regular cuts across which the occupation indicator changes split any
feasible even cell into two consecutive blocks, both of odd cardinality.
The sites of the first block are precisely those in the half-open interval
`[y,z)`. Its complement is the contiguous cyclic block through the period. -/
theorem odd_blocks_between_cuts {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {y z : ℝ} (hyz : y ≤ z)
    (hdiff : ¬(y ∈ inCell hN x ↔ z ∈ inCell hN x)) :
    ∃ p q k l : ℕ, p ≤ q ∧ q ≤ 2*m ∧
      q-p = 2*k+1 ∧ 2*m-(q-p)=2*l+1 ∧ k+l+1=m ∧
      ∀ i < 2*m, (y ≤ angle hN x i ∧ angle hN x i < z) ↔ p ≤ i ∧ i < q := by
  obtain ⟨p,hp,hpy⟩ := exists_cut _ (angle_monotone hx) y (2*m)
  obtain ⟨q,hq,hqz⟩ := exists_cut _ (angle_monotone hx) z (2*m)
  have hpq : p ≤ q := by
    by_contra! h
    have hqm : q < 2*m := by omega
    have hy := (hpy q hqm).mpr h
    have hz := (hqz q hqm).mp (hy.trans_le hyz)
    omega
  rw [inCell_iff_cut_odd hp hpy, inCell_iff_cut_odd hq hqz] at hdiff
  refine ⟨p,q,(q-p)/2,(2*m-(q-p))/2,hpq,hq,by omega,by omega,by omega,?_⟩
  intro i hi
  rw [← not_lt, hpy i hi, hqz i hi, not_lt]

/-- Opposite indicators at arbitrary angular cuts transfer to the labelled
period, regardless of whether one of the two cuts crosses the cell origin. -/
theorem odd_blocks_circle_cuts {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {y z : ℝ} (hy : y ∈ circleSet hN x)
    (hz : z ∉ circleSet hN x) :
    let a := cutRepresentative hN x y
    let b := cutRepresentative hN x z
    ∃ p q k l : ℕ, p ≤ q ∧ q ≤ 2*m ∧
      q-p = 2*k+1 ∧ 2*m-(q-p)=2*l+1 ∧ k+l+1=m ∧
      ∀ i < 2*m, (min a b ≤ angle hN x i ∧ angle hN x i < max a b) ↔ p ≤ i ∧ i < q := by
  have hy' := (mem_inCell_cutRepresentative hx y).mpr hy
  have hz' := (mem_inCell_cutRepresentative hx z).not.mpr hz
  dsimp only
  rcases le_total (cutRepresentative hN x y) (cutRepresentative hN x z) with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact odd_blocks_between_cuts hx h (fun e => hz' (e.mp hy'))
  · rw [min_eq_right h, max_eq_left h]
    exact odd_blocks_between_cuts hx h (fun e => hz' (e.mpr hy'))

end GaussianChains.Occupation
