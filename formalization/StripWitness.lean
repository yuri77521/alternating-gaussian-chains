import ChainMinimum
import ChainFourier
import StripWitnessModes
import StripWitnessTail
import PackedFaceGeometry
import CertTree
import Mathlib.Tactic.FinCases

/-! A complete rational score-leaf certificate on a nonempty part of the six-site
simplex. It uses the first broad floor slab, [0.070,0.072], and permits three
independent alternating gaps of length up to 0.074. The estimate is recomputed
from the actual structure factors and the infinite high-mode bound. -/
noncomputable section
namespace GaussianChains.Strip

open GaussianChains.PackedFace GaussianChains.Cert

def boxCoordinates (s h : ℝ) (x : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![s, h, x 1-x 0, x 3-x 2, x 5-x 4]

def dimerBox : Box 5 :=
  ![⟨8,9⟩, ⟨7/100,9/125⟩, ⟨7/100,37/500⟩, ⟨7/100,37/500⟩, ⟨7/100,37/500⟩]

def dimerBounds (_ : Box 5) (_ : Quantity) : Interval := ⟨-64,-1/5⟩

theorem dimerLeaf_accepted : accept dimerBounds none dimerBox (.leaf (.score 0)) = true := by
  norm_num [accept,violates,dimerBounds]

def rawScore (s : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-(Real.pi^2)/s)^((k+1)^2)*‖structureFactor x (k+1)‖^2

theorem sixWave_eq (x : Fin 6 → ℝ) (n : ℕ) : structureFactor x n = sixWave x n := by
  change (∑ j : Fin 6, (charge j : ℂ)*wave n (x j)) = _
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  norm_num [charge,sixWave,show (2:Fin 3).succ = 3 by rfl,
    show (2:Fin 4).succ = 3 by rfl,show (2:Fin 5).succ = 3 by rfl,
    show (3:Fin 4).succ = 4 by rfl,show (3:Fin 5).succ = 4 by rfl,
    show (4:Fin 5).succ = 5 by rfl]
  <;> ring

theorem trial_rawScore_lower {s h : ℝ} (hs : 0 < s) (hl : 0 ≤ h) (hr : h ≤ 9/125) :
    Real.exp (-(Real.pi^2)/s)*(5/2) ≤ rawScore s (sites h 0) := by
  have hmode : ‖structureFactor (sites h 0) 1‖^2 =
      4*(2*Real.cos (2*Real.pi*h)-1)^2 := by
    rw [sixWave_eq]
    change ‖wave 1 0-wave 1 h+wave 1 (2*h)-wave 1 (1/2+0)+
      wave 1 (1/2+0+h)-wave 1 (1/2+0+2*h)‖^2 = _
    rw [norm_six_wave_sq]
    simp
    <;> ring
  have hsum := fourier_summable (sites h 0) hs
  rw [rawScore, hsum.tsum_eq_zero_add]
  simp only [zero_add, one_pow, pow_one, hmode]
  refine (mul_le_mul_of_nonneg_left (centered_mode_lower hl hr) (Real.exp_pos _).le).trans ?_
  exact le_add_of_nonneg_right (tsum_nonneg fun k => by positivity)

private theorem dimer_inputs {s h : ℝ} {x : Fin 6 → ℝ}
    (hx : dimerBox.Mem (boxCoordinates s h x)) : 8 ≤ s ∧ s ≤ 9 ∧
      0 ≤ h ∧ h ≤ 9/125 ∧ shortDimers x := by
  have hs : (8:ℝ) ≤ s ∧ s ≤ 9 := by simpa [dimerBox, boxCoordinates, Interval.Mem] using hx 0
  have hh : (7/100:ℝ) ≤ h ∧ h ≤ 9/125 := by
    simpa [dimerBox, boxCoordinates, Interval.Mem] using hx 1
  have hd (a b : ℝ) (hab : (7/100:ℝ) ≤ b-a ∧ b-a ≤ 37/500) :
      |a-b| ≤ 37/500 := abs_le.mpr ⟨by linarith [hab.2], by linarith [hab.1]⟩
  refine ⟨hs.1,hs.2,by linarith [hh.1],hh.2, hd _ _ ?_, hd _ _ ?_, hd _ _ ?_⟩
  · simpa [dimerBox, boxCoordinates, Interval.Mem] using hx 2
  · simpa [dimerBox, boxCoordinates, Interval.Mem] using hx 3
  · simpa [dimerBox, boxCoordinates, Interval.Mem] using hx 4

/-- The exact one-sided rational envelope passed to the score leaf, after the
common strictly positive nome is divided out. -/
theorem dimer_score_enclosure {s h : ℝ} {x : Fin 6 → ℝ}
    (hx : dimerBox.Mem (boxCoordinates s h x)) :
    rawScore s x / Real.exp (-(Real.pi^2)/s) -
      rawScore s (sites h 0) / Real.exp (-(Real.pi^2)/s) ≤ (-1/5:ℝ) := by
  obtain ⟨h8,h9,hh,hr,hd⟩ := dimer_inputs hx
  have hs : 0 < s := by linarith
  let q := Real.exp (-(Real.pi^2)/s)
  have hq : 0 < q := Real.exp_pos _
  have upper := sum_dimer_le hq (nome_cap hs h9)
    (fun n => ‖structureFactor x n‖) (fun _ => norm_nonneg _)
    (fun n => by change ‖structureFactor x n‖ ≤ _; rw [sixWave_eq]; exact dimers_mode_bound hd n)
  change rawScore s x ≤ q*(343/150) at upper
  have lower := trial_rawScore_lower hs hh hr
  change q*(5/2) ≤ rawScore s (sites h 0) at lower
  change rawScore s x / q - rawScore s (sites h 0) / q ≤ _
  rw [← sub_div, div_le_iff₀ hq]
  linarith

theorem dimerBox_trial_feasible {s h : ℝ} {x : Fin 6 → ℝ}
    (hx : dimerBox.Mem (boxCoordinates s h x)) : Feasible (by decide) h (sites h 0) := by
  obtain ⟨_,_,_,hr,_⟩ := dimer_inputs hx
  intro i
  fin_cases i <;> norm_num [gap,liftSite,sites] <;> linarith

/-- A continuous box exclusion for the physical energy model, with all widths,
floors and the near contacts varying throughout the certified box. -/
theorem dimerBox_energy_exclusion {s h : ℝ} {x : Fin 6 → ℝ}
    (hx : dimerBox.Mem (boxCoordinates s h x)) : imageEnergy s (sites h 0) < imageEnergy s x := by
  have hs : 0 < s := by linarith [(dimer_inputs hx).1]
  let q := Real.exp (-(Real.pi^2)/s)
  have hq : 0 < q := Real.exp_pos _
  have hc : rawScore s x / q < rawScore s (sites h 0) / q :=
    score_leaf_excludes dimerLeaf_accepted (by
      simpa [dimerBounds,q] using dimer_score_enclosure hx)
  have hsc := (div_lt_div_iff_of_pos_right hq).mp hc
  rw [imageEnergy_fourier 3 hs (sites h 0), imageEnergy_fourier 3 hs x]
  exact sub_lt_sub_left (mul_lt_mul_of_pos_left hsc (by positivity)) _

/-- The strict interior contains a feasible cell satisfying all six floor constraints. -/
theorem dimerBox_nonempty :
    ∃ x : Fin 6 → ℝ, dimerBox.Mem (boxCoordinates (33/4) (71/1000) x) ∧
      Feasible (by decide) (71/1000) x := by
  let x (i : Fin 6) : ℝ := match i.val with
    | 0 => 0 | 1 => 73/1000 | 2 => 1/3 | 3 => 1/3+73/1000 | 4 => 2/3 | _ => 2/3+73/1000
  use x
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [dimerBox,boxCoordinates,Interval.Mem,gap,liftSite,x]

/-- The physical trial lies in the same admissible simplex at this floor. -/
theorem dimerBox_no_ground_state {s h : ℝ} {x : Fin 6 → ℝ}
    (hx : dimerBox.Mem (boxCoordinates s h x)) : ¬ IsGroundState (by decide) h s x := by
  intro hmin
  exact (dimerBox_energy_exclusion hx).not_ge (hmin.2 _ (dimerBox_trial_feasible hx))

/-- Reversing the sign of the strict score envelope invalidates the terminal. -/
theorem positive_margin_rejected :
    accept (fun _ _ => (⟨-64,1/5⟩ : Interval)) none dimerBox (.leaf (.score 0)) = false := by
  norm_num [accept,violates]

/-- Standalone checker for a supplied rational subbox and a proposed upper
score margin. An envelope stricter than the proved enclosure is rejected.
The width, physical floor and three tested gaps are all interval coordinates. -/
def checkDimer (B : Box 5) (margin : ℚ) : Bool :=
  B.subsetB dimerBox && decide ((-1/5:ℚ) ≤ margin) &&
    accept (fun _ _ => (⟨-64,margin⟩ : Interval)) none B (.leaf (.score 0))

theorem checkDimer_sound {B : Box 5} {margin : ℚ} (ok : checkDimer B margin = true)
    {s h : ℝ} {x : Fin 6 → ℝ} (hx : B.Mem (boxCoordinates s h x)) :
    let q := Real.exp (-(Real.pi^2)/s)
    rawScore s x/q-rawScore s (sites h 0)/q ≤ (margin:ℝ) ∧ margin < 0 ∧
      ¬ IsGroundState (by decide) h s x := by
  simp only [checkDimer,Bool.and_eq_true] at ok
  have hbox := Box.mem_of_subsetB ok.1.1 hx
  have hmargin : (-1/5:ℚ) ≤ margin := of_decide_eq_true ok.1.2
  have hmargin' : (-1/5:ℝ) ≤ (margin:ℝ) := by exact_mod_cast hmargin
  have hneg : margin < 0 := of_decide_eq_true ok.2
  exact ⟨(dimer_score_enclosure hbox).trans hmargin',hneg,dimerBox_no_ground_state hbox⟩

theorem dimer_box_accepted : checkDimer dimerBox (-1/5) = true := by
  have hsub : dimerBox.subsetB dimerBox = true :=
    decide_eq_true (fun _ => (And.intro le_rfl le_rfl))
  norm_num [checkDimer,hsub,accept,violates]

theorem changed_margin_rejected : checkDimer dimerBox (1/5) = false :=
  by norm_num [checkDimer,accept,violates]

theorem unproved_margin_rejected : checkDimer dimerBox (-1/4) = false :=
  by norm_num [checkDimer]

#print axioms checkDimer_sound
#print axioms dimerBox_energy_exclusion
#print axioms dimerBox_no_ground_state
end GaussianChains.Strip
