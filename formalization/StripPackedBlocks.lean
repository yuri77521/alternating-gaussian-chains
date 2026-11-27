import StripChamberReduction
import StripBlockOrder
import Mathlib.Topology.Algebra.Order.Field

/-! Maximal packed blocks in the same working chart as the certificate.
Moving all labels of one block leaves every contact fixed. Both directions
are admissible because the two ends of a maximal block have slack. -/
noncomputable section
namespace GaussianChains.Strip
open Filter Topology

def blockStart (A : Support) (k : ℕ) := ((0::boundaries A)[k]?).getD 0
def blockLength (A : Support) (k : ℕ) := ((blocks A)[k]?).getD 0
def inBlock (A : Support) (k : ℕ) (i : Fin 6) :=
  blockStart A k ≤ i.val ∧ i.val < blockStart A k + blockLength A k

instance (A : Support) (k : ℕ) (i : Fin 6) : Decidable (inBlock A k i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def blockSpeed (A : Support) (k : ℕ) (i : Fin 6) : ℤ := if inBlock A k i then 1 else 0
def neighbor (i : Fin 6) : Fin 6 := ⟨(i.val+1)%6,Nat.mod_lt _ (by decide)⟩

def boundary (A : Support) (i : Fin 6) : Prop := i=5 ∨ ∃ j : Fin 5, j ∈ A ∧ j.castSucc=i
instance (A : Support) (i : Fin 6) : Decidable (boundary A i) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem movements_only_at_boundary : ∀ A : Support, ∀ k i : Fin 6,
    blockSpeed A k (neighbor i) ≠ blockSpeed A k i → boundary A i := by decide

theorem block_bounds : ∀ A : Support, ∀ k : Fin 6, k.val < (blocks A).length →
    1 ≤ blockLength A k ∧ blockStart A k + blockLength A k ≤ 6 := by decide

theorem contacts_inside : ∀ A : Support, ∀ k i : Fin 6, blockStart A k ≤ i.val →
    i.val+1 < blockStart A k+blockLength A k → ¬ boundary A i := by decide

theorem distinguished_slack {x : Fin 6 → ℝ} {h : ℝ} (hh : h < 1/6)
    (hlast : largestLast x) : h < gap positiveSix x 5 := by
  have hs := sum_gap positiveSix x
  have ht := Finset.sum_le_sum (s:=Finset.univ) fun i _ => hlast i
  simp at ht
  linarith

theorem boundary_iff_slack {h : ℝ} (hh : h < 1/6) (x : Fin 6 → ℝ) (hlast : largestLast x)
    (i : Fin 6) : boundary (labelledSupport h x) i ↔ h < gap positiveSix x i := by
  constructor
  · rintro (hi|⟨j,hj,rfl⟩)
    · subst i; exact distinguished_slack hh hlast
    · rw [labelledSupport,mem_active_iff,slack_positive_iff hh] at hj
      exact hj
  · intro hi
    by_cases h5 : i = 5
    · exact Or.inl h5
    · right
      have hlt : i.val < 5 := by
        have hne : i.val ≠ 5 := fun e => h5 (Fin.ext e)
        omega
      let j : Fin 5 := ⟨_,hlt⟩
      refine ⟨j,?_,rfl⟩
      rwa [labelledSupport,mem_active_iff,slack_positive_iff hh]

def shiftBlock (x : Fin 6 → ℝ) (A : Support) (k : Fin 6) (t : ℝ) (i : Fin 6) :=
  x i + t*(blockSpeed A k i : ℝ)

theorem shiftBlock_gap (x : Fin 6 → ℝ) (A : Support) (k i : Fin 6) (t : ℝ) :
    gap positiveSix (shiftBlock x A k t) i = gap positiveSix x i +
      t*((blockSpeed A k (neighbor i):ℝ)-(blockSpeed A k i:ℝ)) := by
  simp only [gap,liftSite,shiftBlock,neighbor,Nat.mod_eq_of_lt i.isLt,Nat.div_eq_of_lt i.isLt]
  ring

theorem shiftBlock_feasible {x : Fin 6 → ℝ} {h : ℝ} (hh : h < 1/6)
    (hx : Feasible positiveSix h x) (hlast : largestLast x) (k : Fin 6) :
    ∀ᶠ t : ℝ in 𝓝 0, Feasible positiveSix h (shiftBlock x (labelledSupport h x) k t) := by
  let A := labelledSupport h x
  change ∀ᶠ t : ℝ in 𝓝 0, ∀ i, h ≤ gap positiveSix (shiftBlock x A k t) i
  rw [Filter.eventually_all]
  intro i
  simp_rw [shiftBlock_gap]
  by_cases he : blockSpeed A k (neighbor i)=blockSpeed A k i
  · simpa [he] using hx i
  · let v := (blockSpeed A k (neighbor i):ℝ)-(blockSpeed A k i:ℝ)
    have hb := (boundary_iff_slack hh x hlast i).mp (movements_only_at_boundary A k i he)
    have hc : ContinuousAt (fun t : ℝ => gap positiveSix x i+t*v) 0 := by fun_prop
    exact (hc.eventually (lt_mem_nhds (show h < gap positiveSix x i+0*v by simpa using hb))).mono
      (fun _ h => h.le)

/-- Consecutive sites inside the actual block are separated by exactly the floor. -/
theorem block_progression {x : Fin 6 → ℝ} {h : ℝ} (hh : h < 1/6)
    (hx : Feasible positiveSix h x) (hlast : largestLast x) (k : Fin 6)
    (hk : k.val < (blocks (labelledSupport h x)).length) :
    let A := labelledSupport h x
    ∀ j < blockLength A k,
      liftSite positiveSix x (blockStart A k+j) = liftSite positiveSix x (blockStart A k)+(j:ℝ)*h := by
  let A := labelledSupport h x
  obtain ⟨_,hbound⟩ := block_bounds A k hk
  intro A' j hj
  change liftSite positiveSix x (blockStart A k+j) = liftSite positiveSix x (blockStart A k)+(j:ℝ)*h
  change j < blockLength A k at hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hlt : blockStart A k+j < 6 := by omega
    let i : Fin 6 := ⟨_,hlt⟩
    have hnc := contacts_inside A k i (show blockStart A k ≤ blockStart A k+j by omega)
      (show blockStart A k+j+1 < blockStart A k+blockLength A k by omega)
    have hgap := le_antisymm (le_of_not_gt fun h => hnc ((boundary_iff_slack hh x hlast i).mpr h)) (hx i)
    have H := gap_lift_period positiveSix x (blockStart A k+j)
    have hf : (⟨(blockStart A k+j)%6,Nat.mod_lt _ positiveSix⟩ : Fin 6) = i := Fin.ext (Nat.mod_eq_of_lt hlt)
    rw [hf] at H
    change _ = gap positiveSix x i at H
    rw [hgap,ih (by omega)] at H
    push_cast
    rw [show blockStart A k+(j+1) = blockStart A k+j+1 by omega]
    linarith

end GaussianChains.Strip
