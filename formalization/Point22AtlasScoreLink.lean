import Point22AtlasCells
import Point22AtlasQuantities
import ChainScore

/-! Every ordered pair of distinct labels with increasing index either lies
within one packed block, or spans two different blocks. This partitions the
actual score at any choices of the block starts, including its variations. -/
noncomputable section
namespace GaussianChains.Point22.Atlas

open Finset

private def label (w : Word) (a : Fin 6) (r : ℕ) : Fin 6 :=
  Fin.ofNat 6 (firstSite w a + r)

private theorem offset_lt (w : Word) : ∀ p : Fin 6, offset w p < blockSize w (blockId w p) := by
  cases w <;> decide

private theorem label_fiber (w : Word) : ∀ (a : Fin 6) (r : Fin (blockSize w a)),
    blockId w (label w a r) = a ∧ offset w (label w a r) = r.val ∧
      (label w a r).val = firstSite w a + r.val := by
  cases w <;> decide

private theorem block_end_le_start (w : Word) : ∀ a b : Fin 6, a < b →
    firstSite w a + blockSize w a ≤ firstSite w b := by
  cases w <;> decide

private theorem active_size (w : Word) : ∀ a : Fin 6, a.val < w.blocks.length ↔
    0 < blockSize w a := by
  cases w <;> decide

private def labelEquiv (w : Word) : (Σ a : Fin 6, Fin (blockSize w a)) ≃ Fin 6 where
  toFun z := label w z.1 z.2
  invFun p := ⟨blockId w p, ⟨offset w p, offset_lt w p⟩⟩
  left_inv := by cases w <;> decide
  right_inv := by cases w <;> decide

private theorem splitLabels (w : Word) (f : Fin 6 → ℝ) :
    (∑ p, f p) = ∑ a : Fin 6, ∑ r : Fin (blockSize w a), f (label w a r) := by
  rw [← (labelEquiv w).sum_comp f, Fintype.sum_sigma]
  rfl

private theorem label_order (w : Word) {a b : Fin 6} (ha : a < b)
    (r : Fin (blockSize w a)) (t : Fin (blockSize w b)) :
    label w a r < label w b t := by
  change (label w a r).val < (label w b t).val
  rw [(label_fiber w a r).2.2, (label_fiber w b t).2.2]
  have h := block_end_le_start w a b ha
  omega

private theorem sign_product (w : Word) {a b : Fin 6} (hab : a ≤ b)
    (r : Fin (blockSize w a)) (t : Fin (blockSize w b)) :
    charge (label w a r) * charge (label w b t) =
      (pairSign w a b : ℝ) * (blockSign r t : ℝ) := by
  have h : firstSite w a ≤ firstSite w b := by
    rcases lt_or_eq_of_le hab with hl | rfl
    · exact (Nat.le_add_right ..).trans (block_end_le_start w a b hl)
    · rfl
  simp only [charge, (label_fiber w a r).2.2, (label_fiber w b t).2.2, pairSign, blockSign,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, ← pow_add]
  rw [show firstSite w a+r.val+(firstSite w b+t.val) =
    (firstSite w b-firstSite w a+(r.val+t.val))+2*firstSite w a by omega, pow_add, pow_mul]
  simp

private theorem placed_diff (w : Word) (y : Fin 6 → ℝ) (a b : Fin 6)
    (r : Fin (blockSize w a)) (t : Fin (blockSize w b)) :
    placed w y (label w b t) - placed w y (label w a r) = y b - y a + (shift r t : ℝ) := by
  simp only [placed, (label_fiber w a r).1, (label_fiber w b t).1,
    (label_fiber w a r).2.1, (label_fiber w b t).2.1, shift]
  push_cast
  ring

private def physicalPair (w : Word) (y : Fin 6 → ℝ) (p q : Fin 6) : ℝ :=
  if p < q then charge p * charge q * kernel 22 (placed w y q - placed w y p) else 0

private def withinBlock (w : Word) (a : Fin 6) : ℝ :=
  ∑ r : Fin (blockSize w a), ∑ t : Fin (blockSize w a),
    if r < t then (blockSign r t : ℝ) * mode 0 (shift r t) else 0

private theorem blockPair_sum (w : Word) (y : Fin 6 → ℝ) (a b : Fin 6) :
    (∑ r : Fin (blockSize w a), ∑ t : Fin (blockSize w b),
      physicalPair w y (label w a r) (label w b t)) =
      (if a = b then withinBlock w a else 0) +
      (if active w a b then (pairSign w a b : ℝ) *
        blockValue (blockSize w a) (blockSize w b) 0 (y b-y a) else 0) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [if_neg hab.ne, zero_add]
    by_cases hb : b.val < w.blocks.length
    · rw [if_pos (show active w a b from ⟨hab, hb⟩)]
      unfold blockValue
      rw [← Fin.sum_univ_eq_sum_range]
      simp_rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro t _
      simp only [physicalPair, if_pos (label_order w hab r t), sign_product w hab.le r t,
        placed_diff, mode, Function.iterate_zero_apply]
      ring
    · have hz : blockSize w b = 0 := by
        have := (active_size w b).not.mp hb
        omega
      haveI : IsEmpty (Fin (blockSize w b)) := hz ▸ inferInstanceAs (IsEmpty (Fin 0))
      simp [active, hb]
  · simp only [active, lt_irrefl, false_and, if_false, add_zero, withinBlock]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro t _
    have hlt : label w a r < label w a t ↔ r < t := by
      change (label w a r).val < (label w a t).val ↔ r.val < t.val
      rw [(label_fiber w a r).2.2,(label_fiber w a t).2.2, Nat.add_lt_add_iff_left]
    simp [physicalPair, hlt, sign_product w le_rfl r t, placed_diff, pairSign, mode]
  · have hterm (r : Fin (blockSize w a)) (t : Fin (blockSize w b)) :
        physicalPair w y (label w a r) (label w b t) = 0 :=
      if_neg (label_order w hab t r).not_gt
    simp [hterm, active, hab.not_gt, hab.ne']

/-- Exact value of the physical pair score, for every word and every placement.
Thus the score and all unrestricted block translations used in the atlas refer
to the same per-cell model. -/
theorem atlasScore_placed (w : Word) (y : Fin 6 → ℝ) :
    pairScore 22 (placed w y) = atlasScore w y (internalScore w) := by
  change (∑ p, ∑ q, physicalPair w y p q) = _
  rw [splitLabels w (fun p => ∑ q, physicalPair w y p q)]
  simp_rw [splitLabels w (physicalPair w y _)]
  have swap (a : Fin 6) :
      (∑ r : Fin (blockSize w a), ∑ b : Fin 6, ∑ t : Fin (blockSize w b),
        physicalPair w y (label w a r) (label w b t)) =
      (∑ b : Fin 6, ∑ r : Fin (blockSize w a), ∑ t : Fin (blockSize w b),
        physicalPair w y (label w a r) (label w b t)) := sum_comm
  simp_rw [swap, blockPair_sum, sum_add_distrib]
  simp only [sum_ite_eq, mem_univ, if_true]
  simp only [atlasScore, directional, pow_zero, mul_one, internalScore]
  congr 1
  apply sum_congr rfl
  intro a _
  simp only [withinBlock, Fin.lt_def]
  simp_rw [← Fin.sum_univ_eq_sum_range]

#print axioms atlasScore_placed
end GaussianChains.Point22.Atlas
