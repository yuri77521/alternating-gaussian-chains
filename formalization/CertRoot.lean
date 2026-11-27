import CertRootNumbers
import CertRootTail
import CertTree
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-! The root enclosure in Eq. (12) of the frozen manuscript, for the
derivative of the signed unordered score along the reflection-fixed line. -/

namespace GaussianChains.Root22
open Set GaussianChains.CertExp

/-- Half of the score derivative on the 3111 reflection line. -/
noncomputable def halfSlope (r : ℝ) : ℝ :=
  -(derivKernel (r-1/1000) - derivKernel r + derivKernel (r+1/1000)) +
    derivKernel (1/2-r) - derivKernel (1-2*r)

/-- The sign convention for Eq. (13): the score's half-derivative is the
negative of the scalar force printed in the paper. -/
theorem paper_force_eq (r : ℝ) :
    derivKernel (r-1/1000) - derivKernel r + derivKernel (r+1/1000) -
      derivKernel (1/2-r) - derivKernel (2*r) = -halfSlope r := by
  rw [halfSlope, derivKernel_one_sub]
  ring

theorem derivativeBox_sound {d : ℚ} (hd : -1 ≤ d ∧ d ≤ 1) :
    Encloses (derivativeBox d) (derivKernel (d:ℝ)) := by
  have he : ExpBound negExpBox := fun {_} hx hmax => negExpBox_sound hx hmax
  have hmid : Encloses (retained negExpBox d) (finiteKernel (d:ℝ)) :=
    retained_sound he hd
  have ha : |(d:ℝ)| ≤ 1 := abs_le.mpr (by exact_mod_cast hd)
  have ht := abs_le.mp (tail_bound ha)
  have hr : Encloses (-tailRadius, tailRadius)
      (derivKernel (d:ℝ) - finiteKernel (d:ℝ)) := by
    simpa [Encloses, tailRadius] using ht
  simpa [derivativeBox] using addBox_sound hmid hr

theorem slopeBox_sound {r : ℚ} (hr : 1/5 ≤ r ∧ r ≤ 3/10) :
    Encloses (slopeBox r) (halfSlope (r:ℝ)) := by
  have h₁ := derivativeBox_sound (d := r) (by constructor <;> linarith [hr.1,hr.2])
  have h₂ := derivativeBox_sound (d := r-1/1000) (by constructor <;> linarith [hr.1,hr.2])
  have h₃ := derivativeBox_sound (d := r+1/1000) (by constructor <;> linarith [hr.1,hr.2])
  have h₄ := derivativeBox_sound (d := 1/2-r) (by constructor <;> linarith [hr.1,hr.2])
  have h₅ := derivativeBox_sound (d := 1-2*r) (by constructor <;> linarith [hr.1,hr.2])
  have H := subBox_sound (addBox_sound (subBox_sound (subBox_sound h₁ h₂) h₃) h₄) h₅
  push_cast at H
  unfold halfSlope
  rw [show -(derivKernel ((r:ℝ)-1/1000) - derivKernel r + derivKernel ((r:ℝ)+1/1000)) =
    derivKernel r - derivKernel ((r:ℝ)-1/1000) - derivKernel ((r:ℝ)+1/1000) by ring]
  exact H

theorem halfSlope_pos : 0 < halfSlope (lowerRoot:ℝ) :=
  signCheck_pos_sound (slopeBox_sound (by norm_num [lowerRoot])) check_lower

theorem halfSlope_neg : halfSlope (upperRoot:ℝ) < 0 :=
  signCheck_neg_sound (slopeBox_sound (by norm_num [upperRoot])) check_upper

def certInterval (b : Box) : GaussianChains.Cert.Interval := ⟨b.1, b.2⟩

theorem bracket_accepted :
    GaussianChains.Cert.checkBracket (certInterval (slopeBox lowerRoot))
      (certInterval (slopeBox upperRoot)) = true := by
  have hl : 0 < (slopeBox lowerRoot).1 := by simpa [signCheck] using check_lower
  have hu : (slopeBox upperRoot).2 < 0 := by simpa [signCheck] using check_upper
  exact decide_eq_true (Or.inr ⟨hl,hu⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Deliberately assigning the wrong sign at the right endpoint is rejected. -/
theorem wrong_upper_sign_rejected : signCheck (slopeBox upperRoot) true = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Negating the entire right endpoint enclosure destroys the real bracket. -/
theorem mutated_bracket_rejected :
    GaussianChains.Cert.checkBracket (certInterval (slopeBox lowerRoot))
      (certInterval (slopeBox upperRoot)).neg = false := by decide +kernel

theorem halfSlope_continuousOn :
    ContinuousOn halfSlope (Icc (lowerRoot:ℝ) (upperRoot:ℝ)) := by
  have compK (f : ℝ → ℝ) (hc : Continuous f)
      (hm : MapsTo f (Icc (lowerRoot:ℝ) (upperRoot:ℝ)) (Icc (-1) 1)) :
      ContinuousOn (fun r => derivKernel (f r)) (Icc (lowerRoot:ℝ) (upperRoot:ℝ)) :=
    continuousOn_derivKernel.comp hc.continuousOn hm
  have hbounds {x : ℝ} (hx : x ∈ Icc (lowerRoot:ℝ) (upperRoot:ℝ)) :
      1/5 ≤ x ∧ x ≤ 3/10 := by
    exact ⟨(by norm_num [lowerRoot] : (1:ℝ)/5 ≤ (lowerRoot:ℝ)).trans hx.1,
      hx.2.trans (by norm_num [upperRoot])⟩
  have h₁ := compK (fun r => r-1/1000) (by fun_prop)
    (by intro x hx; rcases hbounds hx with ⟨hl,hu⟩; constructor <;> dsimp <;> linarith)
  have h₂ := compK id continuous_id
    (by intro x hx; rcases hbounds hx with ⟨hl,hu⟩; constructor <;> dsimp <;> linarith)
  have h₃ := compK (fun r => r+1/1000) (by fun_prop)
    (by intro x hx; rcases hbounds hx with ⟨hl,hu⟩; constructor <;> dsimp <;> linarith)
  have h₄ := compK (fun r => 1/2-r) (by fun_prop)
    (by intro x hx; rcases hbounds hx with ⟨hl,hu⟩; constructor <;> dsimp <;> linarith)
  have h₅ := compK (fun r => 1-2*r) (by fun_prop)
    (by intro x hx; rcases hbounds hx with ⟨hl,hu⟩; constructor <;> dsimp <;> linarith)
  exact (((h₁.sub h₂).add h₃).neg.add h₄).sub h₅

/-- A zero of the *infinite* derivative image sum lies strictly inside the
published 30-decimal bracket. Uniqueness requires the separate concavity argument. -/
theorem reflection_root_enclosed :
    ∃ r : ℝ, (lowerRoot:ℝ) < r ∧ r < (upperRoot:ℝ) ∧ halfSlope r = 0 := by
  have hs := GaussianChains.Cert.bracket_sound bracket_accepted
    (a := halfSlope lowerRoot) (b := halfSlope upperRoot)
    (slopeBox_sound (by norm_num [lowerRoot])) (slopeBox_sound (by norm_num [upperRoot]))
  obtain ⟨hl,hu⟩ := hs.resolve_left (fun h => (not_lt_of_ge halfSlope_pos.le) h.1)
  obtain ⟨r,hr,he⟩ := intermediate_value_Ioo'
    (by norm_num [lowerRoot, upperRoot] : (lowerRoot:ℝ) ≤ (upperRoot:ℝ))
    halfSlope_continuousOn (show (0:ℝ) ∈ Ioo _ _ from ⟨hu,hl⟩)
  exact ⟨r, hr.1, hr.2, he⟩

theorem paper_force_root_enclosed :
    ∃ r : ℝ, (lowerRoot:ℝ) < r ∧ r < (upperRoot:ℝ) ∧
      derivKernel (r-1/1000) - derivKernel r + derivKernel (r+1/1000) -
        derivKernel (1/2-r) - derivKernel (2*r) = 0 := by
  obtain ⟨r, hl, hu, h⟩ := reflection_root_enclosed
  exact ⟨r, hl, hu, by rw [paper_force_eq, h, neg_zero]⟩

#print axioms reflection_root_enclosed
#print axioms paper_force_root_enclosed
#print axioms wrong_upper_sign_rejected
#print axioms mutated_bracket_rejected

end GaussianChains.Root22
