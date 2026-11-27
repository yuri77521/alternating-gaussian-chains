import BandVerifiedCacheClaims
import BandVerifiedCacheInstance
import BandVerifiedCacheRange

namespace GaussianChains.Band.Fast
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds

private theorem Checked.node {a : Fin 3} (c : Checked a) {p : ℕ} (hp : p ≤ 8192) :
    validateNode a p = true := by
  rcases lt_or_eq_of_le hp with h | rfl
  · exact runChecks_sound 13 0 c.grid (Nat.zero_le _) h
  · exact c.last

theorem Checked.raw_eq {a : Fin 3} (c : Checked a) (j : Order) {p : ℕ} (hp : p ≤ 8192) :
    rawBox a j p = stripNode (Fixed.s a) j p := by
  have hpage (b : ℕ) (hb : b < 1024) : validatePage a b = true :=
    runChecks_sound 10 0 c.recurrence (Nat.zero_le _) hb
  have h := Fixed.row_eq_gridNode a (sample := gauss a) (fun _ => gauss_eq c.init hpage) j hp
  have hr := of_decide_eq_true (Bool.and_eq_true_iff.mp (order_checked (c.node hp) j)).1
  rw [rawBox, hr]
  exact h

private theorem Checked.edge {a : Fin 3} (c : Checked a) (j : Order) {p : ℕ} (hp : p < 8192) :
    edgeOK (fun i => (rawTicks a j i).1) (turning a j).1 (turning a j).2
      (ascending j) (!(ascending j)) (lastAscending j) p = true ∧
    edgeOK (fun i => (rawTicks a j i).2) (turning a j).1 (turning a j).2
      (ascending j) (!(ascending j)) (lastAscending j) p = true := by
  have h := (Bool.and_eq_true_iff.mp (order_checked (c.node hp.le) j)).2
  simpa only [decide_eq_false (Nat.not_le.mpr hp), Bool.false_or, Bool.and_eq_true] using h

private theorem turning_le (a : Fin 3) (j : Order) : (turning a j).1 ≤ (turning a j).2 := by
  fin_cases a <;> cases j <;> decide

private theorem pad_eq (a : Fin 3) (j : Order) (p : ℕ) :
    paddedNode 8192 1000000000 (stripCap j) (rawBox a j) p =
      tickBox ((rawTicks a j p).1 - paddingTicks j) ((rawTicks a j p).2 + paddingTicks j) := by
  have h : ⌈stripCap j / (2*(8192:ℚ)) * (1000000000:ℚ)⌉ = paddingTicks j := by
    cases j <;> decide +kernel
  simp only [paddedNode, pad, rawBox, tickBox]
  change _ = (⟨_,_⟩ : Interval)
  rw [show ⌈stripCap j / (2*((8192:ℕ+):ℚ)) * ((1000000000:ℕ+):ℚ)⌉ = paddingTicks j from h]
  congr 1 <;> push_cast <;> ring

private theorem anchor_eq (s : Slab) : Fixed.s (anchorId s) = s.anchor := by
  cases s <;> decide +kernel

theorem packetCache_valid (s : Slab) (c : Checked (anchorId s)) : Valid s (packetCache s) := by
  constructor
  · intro j p hp
    change (rawBox (anchorId s) j p).Mem _
    rw [c.raw_eq j hp, anchor_eq]
    exact gridNode_strip_sound _ _ (s := s.anchor) (by cases s <;> norm_num [Slab.anchor, Set.mem_Icc]) j hp
  · intro j l p r hL hR hlast
    let a := anchorId s
    have left := (range_sound (turning_le a j) (fun _ hp => (c.edge j hp).1) hL hR hlast).1
    have right := (range_sound (turning_le a j) (fun _ hp => (c.edge j hp).2) hL hR hlast).2
    change (lookupBox a j l r).lo ≤ (paddedNode 8192 1000000000 (stripCap j) (rawBox a j) p).lo ∧
      (paddedNode 8192 1000000000 (stripCap j) (rawBox a j) p).hi ≤ (lookupBox a j l r).hi
    rw [pad_eq]
    constructor
    · apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ) ≤ 1000000000)
      exact_mod_cast sub_le_sub_right left (paddingTicks j)
    · apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ) ≤ 1000000000)
      exact_mod_cast add_le_add right (le_refl (paddingTicks j))

end GaussianChains.Band.Fast
