import Point22Contacts
import ChainGeometry
import Mathlib.Data.Fin.VecNotation

/-! The maximal packed blocks supply exact coordinates for all six labels,
including the one-block and all-slack words. -/

namespace GaussianChains.Point22.Atlas

def base (w : Word) (i : Fin 6) := (w.blocks.take i.val).sum
def cellBlockSize (w : Word) (i : Fin 6) := w.blocks[i.val]?.getD 0

def belongs (w : Word) (b p : Fin 6) : Bool :=
  decide (base w b ≤ p.val ∧ p.val < base w b+cellBlockSize w b)

def blockId (w : Word) (p : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? (fun b => belongs w b p)).getD 0

def offset (w : Word) (p : Fin 6) := p.val - base w (blockId w p)

def baseLabel (w : Word) (i : Fin 6) : Fin 6 := Fin.ofNat 6 (base w i)

theorem label_facts (w : Word) (p : Fin 6) :
    (blockId w p).val < w.blocks.length ∧ base w (blockId w p) < 6 ∧
    base w (blockId w p) + offset w p = p.val ∧
    ∀ j : Fin 6, base w (blockId w p) ≤ j.val → j.val < p.val → w.cuts j = false := by
  cases w <;> revert p <;> decide

theorem contact_inside_block (w : Word) (i : Fin 6) (hi : w.cuts i = false) :
    blockId w (i+1) = blockId w i := by
  cases w <;> revert i <;> decide

noncomputable def placed (w : Word) (y : Fin 6 → ℝ) (p : Fin 6) : ℝ :=
  y (blockId w p)+(offset w p:ℝ)/1000

noncomputable def starts (w : Word) (x : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  if i.val < w.blocks.length then x (baseLabel w i)-x 0 else 0

private theorem run_of_contacts {x : Fin 6 → ℝ} (s n : ℕ)
    (hc : ∀ j < n, liftSite (by decide) x (s+j+1) - liftSite (by decide) x (s+j) = 1/1000) :
    liftSite (by decide) x (s+n) = liftSite (by decide) x s+(n:ℝ)/1000 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun j hj => hc j (Nat.lt_succ_of_lt hj))
    have he := hc n (Nat.lt_succ_self n)
    rw [Nat.add_succ]
    push_cast
    linarith

theorem physical_placed_of_cuts (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x)
    (hg : ∀ i, actualCuts (1/1000) (gap (by decide) x) i = w.cuts i) (p : Fin 6) :
    x p = placed w (starts w x) p + x 0 := by
  obtain ⟨ha,hb,hp,hc⟩ := label_facts w p
  let b := base w (blockId w p)
  let n := offset w p
  have he := run_of_contacts (x:=x) b n (fun j hj => by
    have hlt : b+j < 6 := by dsimp [b,n] at *; omega
    let k : Fin 6 := ⟨b+j,hlt⟩
    have hgap : gap (by decide) x k = 1/1000 := by
      apply le_antisymm _ (hx k)
      have hh := (hg k).trans (hc k (Nat.le_add_right _ _) (by dsimp [k,b,n] at *; omega))
      simpa [actualCuts] using hh
    rw [gap_eq_lift_sub] at hgap
    exact hgap)
  have hbase : (baseLabel w (blockId w p)).val = b := Nat.mod_eq_of_lt hb
  have hp' : b+n = p.val := hp
  rw [hp',liftSite_fin,← hbase,liftSite_fin] at he
  simp only [placed,starts,if_pos ha]
  dsimp [n] at he
  linarith

/-- Finite translates of the site labels representing a contact block. -/
theorem starts_fill (w : Word) (p : Fin 6)
    (ha : p.val < w.blocks.length) :
    blockId w (baseLabel w p) = p ∧ offset w (baseLabel w p) = 0 := by
  cases w <;> revert p <;> decide

theorem starts_zero (w : Word) (x : Fin 6 → ℝ) : starts w x 0 = 0 := by
  cases w <;> simp [starts,baseLabel,base,Word.blocks]

theorem inactive_start (w : Word) (x : Fin 6 → ℝ) (p : Fin 6)
    (hp : w.blocks.length ≤ p.val) : starts w x p = 0 :=
  if_neg (Nat.not_lt.mpr hp)

end GaussianChains.Point22.Atlas
