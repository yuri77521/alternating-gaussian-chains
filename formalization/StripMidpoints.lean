import StripPackedBlocks
import StripEvenArcs

/-! The actual ordered block midpoints and their closing step across the period.
These formulas also provide the minimum separations used in the all-even case. -/
noncomputable section
namespace GaussianChains.Strip
open Real

def blockCount (A : Support) := (blocks A).length
def startLift (A : Support) (i : ℕ) := if i=blockCount A then 6 else blockStart A i
def lengthLift (A : Support) (i : ℕ) := if i=blockCount A then blockLength A 0 else blockLength A i

theorem count_bounds : ∀ A : Support, 1 ≤ blockCount A ∧ blockCount A ≤ 6 ∧
    (peakList A).length = blockCount A ∧ blockStart A 0 = 0 := by decide

theorem consecutive_starts : ∀ A : Support, ∀ k : Fin 6, k.val < blockCount A →
    startLift A (k.val+1) = startLift A k+lengthLift A k ∧
    0 < lengthLift A k ∧ 0 < lengthLift A (k.val+1) := by decide

def blockMid (x : Fin 6 → ℝ) (h : ℝ) (A : Support) (k : ℕ) : ℝ :=
  2*π*(liftSite positiveSix x (startLift A k)+((lengthLift A k:ℝ)-1)*h/2)

theorem mid_close (x : Fin 6 → ℝ) (h : ℝ) (A : Support) :
    blockMid x h A (blockCount A) = blockMid x h A 0 + 2*π := by
  have hpos := (count_bounds A).1
  have hstart := (count_bounds A).2.2.2
  have hp := liftSite_add_period positiveSix x 0
  rw [Nat.zero_add] at hp
  simp [blockMid,startLift,lengthLift,show 0 ≠ blockCount A by omega,hstart,hp]
  <;> ring

theorem lift_span {h : ℝ} {x : Fin 6 → ℝ} (hx : Feasible positiveSix h x) (n ℓ : ℕ) :
    liftSite positiveSix x n + (ℓ:ℝ)*h ≤ liftSite positiveSix x (n+ℓ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hgap := hx ⟨(n+ℓ)%6,Nat.mod_lt _ positiveSix⟩
    rw [← gap_lift_period] at hgap
    push_cast
    change _ ≤ liftSite positiveSix x (n+ℓ+1)
    linarith

theorem mid_step {x : Fin 6 → ℝ} {h : ℝ} (hx : Feasible positiveSix h x) (A : Support)
    (k : ℕ) (hk : k < blockCount A) :
    ((lengthLift A k:ℝ)+(lengthLift A (k+1):ℝ))*(2*π*h)/2 ≤
      blockMid x h A (k+1)-blockMid x h A k := by
  have h6 := (count_bounds A).2.1
  have he := (consecutive_starts A ⟨k,by omega⟩ hk).1
  change startLift A (k+1) = startLift A k + lengthLift A k at he
  have hspan := lift_span hx (startLift A k) (lengthLift A k)
  rw [← he] at hspan
  dsimp only [blockMid]
  nlinarith only [mul_le_mul_of_nonneg_left hspan pi_pos.le]

def InPeakArcs (x : Fin 6 → ℝ) (h : ℝ) (A : Support) (d : ℝ) :=
  ∀ k < blockCount A, ∃ m : ℤ,
    |blockMid x h A k - ((peakIndex A k:ℝ)*(π/2)+2*π*(m:ℝ))| ≤ d

theorem physical_peak_order {x : Fin 6 → ℝ} {h d : ℝ} (hh : 0 ≤ h)
    (hx : Feasible positiveSix h x) (A : Support) (hd : 2*d < π/2) (harcs : InPeakArcs x h A d) :
    descents (peakIndex A) (peakList A).length ≤ 1 := by
  let K := blockCount A
  have hK := count_bounds A
  have h0 : 0 < K := hK.1
  choose pick hfit using harcs
  let τ (k : ℕ) : ℤ := if hk : k < K then pick k hk else pick 0 h0+1
  have hpK : peakIndex A K = peakIndex A 0 := by simp [K,peakIndex,hK.2.2.1]
  have hp : ∀ A : Support, ∀ k : Fin 7, peakIndex A k < 4 := by decide
  have hturn := peak_one_turn hd (peakIndex A) τ (blockMid x h A)
    (fun i hi => hp A ⟨i,by omega⟩) (show τ K = τ 0+1 by simp [τ,h0])
  rw [hK.2.2.1]
  apply hturn
  · intro k hk
    have H := mid_step hx A k hk
    have hnonneg : 0 ≤ ((lengthLift A k:ℝ)+(lengthLift A (k+1):ℝ))*(2*π*h)/2 := by positivity
    linarith
  · intro k hk
    rcases lt_or_eq_of_le hk with hk|rfl
    · simp only [τ,dif_pos hk]
      convert hfit k hk using 2 <;> ring
    · have hf := hfit 0 h0
      rw [show blockMid x h A K = blockMid x h A 0+2*π from mid_close x h A]
      simp only [τ,lt_irrefl,dif_neg,hpK]
      push_cast
      convert hf using 2 <;> ring

end GaussianChains.Strip
