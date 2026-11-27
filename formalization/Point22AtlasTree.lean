import Point22AtlasData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Replay the published closed-box convention for all twelve width-22 trees.
Cube coordinates are integer mesh ticks. Tightening uses only constraints that
hold throughout the contact face. A missing branch is rejected even when the
cut is at an endpoint. -/

namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

def sizeAt (w : Word) (i : Fin 6) : ℕ := w.blocks[i.val]?.getD 0
def startLabel (w : Word) (i : Fin 6) : ℕ := (w.blocks.take i.val).sum

def Active (w : Word) (i : Fin 6) : Prop := i.val < w.blocks.length
instance instDecidableActiveBlock (w : Word) (i : Fin 6) : Decidable (Active w i) := Nat.decLt _ _

/-- Necessary floor constraints on successive starts, including the size of the whole block. -/
def OrderedTicks (w : Word) (x : Fin 6 → ℝ) : Prop :=
  ∀ i : Fin 5, Active w i.succ → 32 * (sizeAt w i.castSucc : ℝ) ≤ x i.succ - x i.castSucc

def lowerStep (w : Word) (B : Box 6) (i : Fin 5) : Box 6 :=
  if Active w i.succ then
    Function.update B i.succ
      ⟨max (B i.succ).lo ((B i.castSucc).lo + 32 * sizeAt w i.castSucc), (B i.succ).hi⟩
  else B

def upperStep (w : Word) (B : Box 6) (i : Fin 5) : Box 6 :=
  if Active w i.succ then
    Function.update B i.castSucc
      ⟨(B i.castSucc).lo, min (B i.castSucc).hi ((B i.succ).hi - 32 * sizeAt w i.castSucc)⟩
  else B

private theorem lowerStep_mem {w : Word} {B : Box 6} {x} (hx : B.Mem x)
    (ho : OrderedTicks w x) (i : Fin 5) : (lowerStep w B i).Mem x := by
  by_cases ha : Active w i.succ
  · intro j
    by_cases hj : j = i.succ
    · subst j
      simp only [lowerStep, ha, if_true, Function.update_self, Interval.Mem,
        Rat.cast_max, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
      exact ⟨max_le (hx _).1 (by linarith [(hx i.castSucc).1,ho i ha]), (hx _).2⟩
    · simpa [lowerStep,ha,Function.update_of_ne hj] using hx j
  · simpa [lowerStep,ha] using hx

private theorem upperStep_mem {w : Word} {B : Box 6} {x} (hx : B.Mem x)
    (ho : OrderedTicks w x) (i : Fin 5) : (upperStep w B i).Mem x := by
  by_cases ha : Active w i.succ
  · intro j
    by_cases hj : j = i.castSucc
    · subst j
      simp only [upperStep,ha,if_true, Function.update_self, Interval.Mem,
        Rat.cast_min, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
      exact ⟨(hx _).1, le_min (hx _).2 (by linarith [(hx i.succ).2,ho i ha])⟩
    · simpa [upperStep,ha,Function.update_of_ne hj] using hx j
  · simpa [upperStep,ha] using hx

private theorem fold_mem (f : Box 6 → Fin 5 → Box 6) {x : Fin 6 → ℝ}
    (hf : ∀ B, B.Mem x → ∀ i, (f B i).Mem x) (l : List (Fin 5)) (B : Box 6) (hx : B.Mem x) :
    (l.foldl f B).Mem x := by
  induction l generalizing B with
  | nil => exact hx
  | cons i l ih => exact ih _ (hf B hx i)

def narrow (w : Word) (B : Box 6) : Box 6 :=
  (List.finRange 5).reverse.foldl (upperStep w) ((List.finRange 5).foldl (lowerStep w) B)

theorem narrow_mem {w : Word} {B : Box 6} {x} (hx : B.Mem x) (ho : OrderedTicks w x) :
    (narrow w B).Mem x := by
  apply fold_mem _ (fun _ hb => upperStep_mem hb ho)
  exact fold_mem _ (fun _ hb => lowerStep_mem hb ho) _ _ hx

def lastIndex (w : Word) : Fin 6 := ⟨min (w.blocks.length-1) 5, by omega⟩

def rootBox (w : Word) : Box 6 := fun i =>
  if i.val=0 ∨ ¬Active w i then ⟨0,0⟩
  else ⟨0,32000-32*sizeAt w (lastIndex w)⟩

def localTarget : Box 6 :=
  fun i =>
    let c : ℚ := match i.val with
      | 1 => 8032 | 2 => 16032 | 3 => 24032 | _ => 0
    ⟨c-2,c+2⟩

/-- Values at indices at which the cyclic block spelling is unchanged. -/
def sameStart (w : Word) (i : Fin 6) : Bool :=
  decide (0 < i.val ∧ Active w i ∧ w.blocks.drop i.val ++ w.blocks.take i.val = w.blocks)

def prevIndex (i : Fin 6) : Fin 6 := ⟨i.val-1, by omega⟩

def CanonicalTicks (w : Word) (x : Fin 6 → ℝ) : Prop :=
  ∀ i, sameStart w i = true →
    x i - x (prevIndex i) - 32*(sizeAt w (prevIndex i)-1 : ℕ) ≤
      32000 - x (lastIndex w) - 32*(sizeAt w (lastIndex w)-1 : ℕ)

def orderCut (w : Word) (B : Box 6) (k : ℕ) : Bool :=
  if hk : k < 6 then
    decide ((B ⟨k,hk⟩).hi < (B ⟨k,hk⟩).lo)
  else if hk' : k-6 < 6 then
    let i : Fin 6 := ⟨k-6,hk'⟩
    sameStart w i && decide (32000 - (B (lastIndex w)).lo - 32*(sizeAt w (lastIndex w)-1 : ℕ) <
      (B i).lo - (B (prevIndex i)).hi - 32*(sizeAt w (prevIndex i)-1 : ℕ))
  else false

theorem orderCut_sound {w : Word} {B : Box 6} {x} (hx : B.Mem x)
    (hc : CanonicalTicks w x) (k : ℕ) : orderCut w B k ≠ true := by
  unfold orderCut
  split
  · intro h
    have hh : ((B ⟨k,by assumption⟩).hi:ℝ) < (B ⟨k,by assumption⟩).lo := by
      exact_mod_cast (of_decide_eq_true h)
    exact hh.not_ge ((hx _).1.trans (hx _).2)
  · split
    · intro h
      dsimp only at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hs,hm⟩ := h
      let i : Fin 6 := ⟨k-6,by assumption⟩
      have hh : (32000:ℝ) - (B (lastIndex w)).lo - 32*(sizeAt w (lastIndex w)-1 : ℕ) <
          (B i).lo - (B (prevIndex i)).hi - 32*(sizeAt w (prevIndex i)-1 : ℕ) := by
        exact_mod_cast (of_decide_eq_true hm)
      linarith only [hh, hc i hs, (hx i).1, (hx (prevIndex i)).2, (hx (lastIndex w)).1]
    · decide

def replay (w : Word) (bounds : Box 6 → Quantity → Interval) (B : Box 6) : Tree 6 → Bool
  | .hole => false
  | .leaf (.feasible k) => orderCut w (narrow w B) k
  | .leaf k => violates k (bounds (narrow w B) k)
  | .localDomain => decide (w = .threeOneOneOne) && (narrow w B).subsetB localTarget
  | .split i t left right =>
    let C := narrow w B
    decide ((C i).lo ≤ t ∧ t ≤ (C i).hi) &&
      replay w bounds (C.Left i t) left && replay w bounds (C.Right i t) right

theorem replay_sound {w : Word} {bounds : Box 6 → Quantity → Interval} {x : Fin 6 → ℝ}
    (ho : OrderedTicks w x) (hc : CanonicalTicks w x)
    (H : ∀ B, B.Mem x → ∀ k, (∀ j, k ≠ .feasible j) → violates k (bounds B k) ≠ true)
    (t : Tree 6) (B : Box 6) (hx : B.Mem x) (ht : replay w bounds B t = true) :
    w = .threeOneOneOne ∧ localTarget.Mem x := by
  induction t generalizing B with
  | hole => simp [replay] at ht
  | localDomain =>
    simp only [replay,Bool.and_eq_true] at ht
    obtain ⟨h₁,h₂⟩ := ht
    exact ⟨of_decide_eq_true h₁, Box.mem_of_subsetB h₂ (narrow_mem hx ho)⟩
  | leaf k =>
    cases k with
    | feasible k => exact (orderCut_sound (narrow_mem hx ho) hc k ht).elim
    | score k => exact (H _ (narrow_mem hx ho) (.score k) (by simp) ht).elim
    | gradient k => exact (H _ (narrow_mem hx ho) (.gradient k) (by simp) ht).elim
    | curvature k => exact (H _ (narrow_mem hx ho) (.curvature k) (by simp) ht).elim
  | split i cut left right il ir =>
    obtain ⟨⟨_,hl⟩,hr⟩ := by simpa only [replay, Bool.and_eq_true] using ht
    rcases Box.split_cover (narrow_mem hx ho) i cut with h | h
    · exact il _ h hl
    · exact ir _ h hr

end GaussianChains.Point22.Atlas
