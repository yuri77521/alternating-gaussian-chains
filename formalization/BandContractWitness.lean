import BandTree
import Mathlib.Data.Fin.VecNotation

/-! A certificate for both chamber-contraction rounds in the support search.
Each of the integer vectors supplied by the producer is checked directly.
No reduction of a nested function-valued `contract (contract B)` is required. -/
namespace GaussianChains.Band
open GaussianChains.Cert

structure ChamberBox where
  lo : Fin 6 → ℤ
  hi : Fin 6 → ℤ

structure ChamberPass where
  raised : Fin 6 → ℤ
  lowered : Fin 6 → ℤ
  out : ChamberBox

def chamberTick (z : ℤ) : ℚ := (z:ℚ)/8192

def ChamberBox.toBox (B : ChamberBox) : Box 6 := fun i => ⟨chamberTick (B.lo i), chamberTick (B.hi i)⟩

/-- Parenthesized explicitly to check only six integers. -/
def chamberSum (v : Fin 6 → ℤ) : ℤ :=
  (v 0+v 1)+(v 2+v 3)+(v 4+v 5)

def chamberMax (v : Fin 6 → ℤ) : ℤ :=
  max (max (max (v 0) (v 1)) (max (v 2) (v 3))) (max (v 4) (v 5))

private def sixAll (f : Fin 6 → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5

private theorem sixAll_sound {f : Fin 6 → Bool} (h : sixAll f = true) (i : Fin 6) : f i = true := by
  simp only [sixAll, Bool.and_eq_true] at h
  fin_cases i <;> tauto

/-- The first sum uses the raw high endpoints. The second uses the independently supplied,
already checked new lows. The final pass applies the largest-gap constraint at coordinate 5. -/
def checkChamberPass (raw : ChamberBox) (p : ChamberPass) : Bool :=
  let upperSum := chamberSum raw.hi
  let lowerSum := chamberSum p.raised
  let maximum := chamberMax p.raised
  sixAll fun i => decide (
    p.raised i = max (raw.lo i) (8192-upperSum+raw.hi i) ∧
    p.lowered i = min (raw.hi i) (8192-lowerSum+p.raised i) ∧
    p.out.lo i = (if i=5 then maximum else p.raised i) ∧
    p.out.hi i = min (p.lowered i) (p.lowered 5))

def checkChamber (raw : ChamberBox) (p₁ p₂ : ChamberPass) : Bool :=
  checkChamberPass raw p₁ && checkChamberPass p₁.out p₂

private theorem complementTick (s a : ℤ) :
    chamberTick (8192-s+a) = 1-chamberTick s+chamberTick a := by
  unfold chamberTick
  push_cast
  ring

private theorem maxTick (z w : ℤ) :
    chamberTick (max z w) = max (chamberTick z) (chamberTick w) := by
  simp [chamberTick, max_div_div_right (by norm_num : (0:ℚ) ≤ 8192)]

private theorem minTick (z w : ℤ) :
    chamberTick (min z w) = min (chamberTick z) (chamberTick w) := by
  simp [chamberTick, min_div_div_right (by norm_num : (0:ℚ) ≤ 8192)]

private theorem sumTick (v : Fin 6 → ℤ) :
    (∑ i, chamberTick (v i)) = chamberTick (chamberSum v) := by
  simp [Fin.sum_univ_succ,chamberSum,chamberTick]
  ring

theorem checkChamberPass_sound {raw : ChamberBox} {p : ChamberPass}
    (hp : checkChamberPass raw p = true) {u : Fin 6 → ℝ}
    (hb : raw.toBox.Mem u) (hs : ∑ i, u i = 1) (hm : ∀ i, u i ≤ u 5) :
    p.out.toBox.Mem u := by
  unfold checkChamberPass at hp
  dsimp only at hp
  have h (i : Fin 6) := of_decide_eq_true (sixAll_sound hp i)
  let raised : ChamberBox := ⟨p.raised,raw.hi⟩
  have hr : raised.toBox = raiseLower raw.toBox := by
    funext i
    have hi := (h i).1
    change p.raised i = max (raw.lo i) (8192 - chamberSum raw.hi + raw.hi i) at hi
    simp [raised,ChamberBox.toBox,raiseLower,allBounds,hi,maxTick,complementTick,sumTick]
  let lowered : ChamberBox := ⟨p.raised,p.lowered⟩
  have hl : lowered.toBox = lowerUpper raised.toBox := by
    funext i
    have hi := (h i).2.1
    change p.lowered i = min (raw.hi i) (8192 - chamberSum p.raised + p.raised i) at hi
    simp [raised,lowered,ChamberBox.toBox,lowerUpper,allBounds,hi,minTick,complementTick,sumTick]
  have hrMem : raised.toBox.Mem u := hr ▸ raiseLower_mem hb hs
  have hlMem : lowered.toBox.Mem u := hl ▸ lowerUpper_mem hrMem hs
  have small (i : Fin 6) : (chamberTick (p.raised i):ℝ) ≤ u 5 := (hlMem i).1.trans (hm i)
  have large : (chamberTick (chamberMax p.raised):ℝ) ≤ u 5 := by
    simpa only [chamberMax,maxTick,Rat.cast_max,max_le_iff] using
      And.intro ⟨⟨small 0,small 1⟩,⟨small 2,small 3⟩⟩ ⟨small 4,small 5⟩
  intro i
  refine ⟨?_, ?_⟩
  · change (chamberTick (p.out.lo i):ℝ) ≤ u i
    rw [(h i).2.2.1]
    by_cases he : i = 5
    · subst i
      simpa using large
    · simpa [he] using (hlMem i).1
  · change u i ≤ (chamberTick (p.out.hi i):ℝ)
    rw [(h i).2.2.2,minTick,Rat.cast_min]
    exact le_min (hlMem i).2 ((hm i).trans (hlMem 5).2)

theorem checkChamber_sound {raw : ChamberBox} {p₁ p₂ : ChamberPass}
    (h : checkChamber raw p₁ p₂ = true) {u : Fin 6 → ℝ}
    (hb : raw.toBox.Mem u) (hs : ∑ i, u i = 1) (hm : ∀ i, u i ≤ u 5) :
    p₂.out.toBox.Mem u := by
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
  exact checkChamberPass_sound h₂ (checkChamberPass_sound h₁ hb hs hm) hs hm

/-- Detect impossible simplex sums and intervals with reversed endpoints. It may be used
before either round, as in the early returns of the frozen chamber. -/
def chamberVoid (B : ChamberBox) : Bool :=
  decide (8192 < chamberSum B.lo ∨ chamberSum B.hi < 8192 ∨ ∃ i, B.hi i < B.lo i)

theorem chamberVoid_sound {B : ChamberBox} (h : chamberVoid B = true) {u : Fin 6 → ℝ}
    (hb : B.toBox.Mem u) (hs : ∑ i, u i = 1) : False := by
  have ha : ∀ i, (B.lo i:ℝ) ≤ 8192*u i ∧ 8192*u i ≤ (B.hi i:ℝ) := by
    intro i
    have h' := hb i
    rcases h' with ⟨hl,hu⟩
    change ((chamberTick (B.lo i)):ℝ) ≤ u i at hl
    change u i ≤ ((chamberTick (B.hi i)):ℝ) at hu
    norm_num [chamberTick] at hl hu
    exact ⟨by linarith,by linarith⟩
  have su : (∑ i, 8192*u i) = 8192 := by rw [← Finset.mul_sum,hs,mul_one]
  have sreal (v : Fin 6 → ℤ) : (chamberSum v:ℝ) = ∑ i, (v i:ℝ) := by
    simp [chamberSum,Fin.sum_univ_succ]; ring
  rcases (of_decide_eq_true h : 8192 < chamberSum B.lo ∨ chamberSum B.hi < 8192 ∨
      ∃ i, B.hi i < B.lo i) with l | r | ⟨i,bad⟩
  · have hl : (8192:ℝ) < chamberSum B.lo := by exact_mod_cast l
    rw [sreal] at hl
    linarith [Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ha i).1)]
  · have hu : (chamberSum B.hi:ℝ) < 8192 := by exact_mod_cast r
    rw [sreal] at hu
    linarith [Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ha i).2)]
  · exact (show (B.hi i:ℝ) < B.lo i by exact_mod_cast bad).not_ge ((ha i).1.trans (ha i).2)

#print axioms checkChamber_sound
end GaussianChains.Band
