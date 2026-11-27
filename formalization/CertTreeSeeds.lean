import CertTreeNodes
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Cubic lower and quartic upper seeds used by the fixed-point tables. -/
namespace GaussianChains.Cert.Nodes
open Set Interval

private noncomputable def p₂ (t : ℝ) := 1-t+t^2/2
private noncomputable def p₃ (t : ℝ) := p₂ t - t^3/6
private noncomputable def p₄ (t : ℝ) := p₃ t + t^4/24

private theorem dp₂ (t : ℝ) : HasDerivAt p₂ (-(1-t)) t := by
  convert ((hasDerivAt_id t).const_sub 1).add (((hasDerivAt_id t).fun_pow 2).div_const 2) using 1
  simp
  ring

private theorem dp₃ (t : ℝ) : HasDerivAt p₃ (-p₂ t) t := by
  convert (dp₂ t).sub (((hasDerivAt_id t).fun_pow 3).div_const 6) using 1
  simp [p₂]
  ring

private theorem dp₄ (t : ℝ) : HasDerivAt p₄ (-p₃ t) t := by
  convert (dp₃ t).add (((hasDerivAt_id t).fun_pow 4).div_const 24) using 1
  simp [p₃]
  ring

private theorem zero_to_right {f v : ℝ → ℝ} (df : ∀ t, HasDerivAt f (v t) t)
    (hf : f 0 = 0) (hpos : ∀ t, 0 ≤ t → 0 ≤ v t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  have hm : MonotoneOn f (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t _ => (df t).continuousAt.continuousWithinAt)
    (fun t _ => (df t).hasDerivWithinAt)
    (fun t hm => hpos t (interior_subset hm))
  simpa [hf] using hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht

private theorem exp_polynomial_bounds {t : ℝ} (ht : 0 ≤ t) :
    p₃ t ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ p₄ t := by
  have de (z : ℝ) : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    simpa using ((hasDerivAt_id z).neg.exp)
  have h₂ (z : ℝ) (hz : 0 ≤ z) : 0 ≤ p₂ z - Real.exp (-z) :=
    zero_to_right (fun z => (dp₂ z).sub (de z)) (by norm_num [p₂])
      (fun v _ => by linarith [Real.add_one_le_exp (-v)]) hz
  have h₃ (z : ℝ) (hz : 0 ≤ z) : 0 ≤ Real.exp (-z) - p₃ z :=
    zero_to_right (fun z => (de z).sub (dp₃ z)) (by norm_num [p₃,p₂])
      (fun v hv => by linarith [h₂ v hv]) hz
  have h₄ : 0 ≤ p₄ t - Real.exp (-t) :=
    zero_to_right (fun z => (dp₄ z).sub (de z)) (by norm_num [p₄,p₃,p₂])
      (fun v hv => by linarith [h₃ v hv]) ht
  exact ⟨sub_nonneg.mp (h₃ t ht), sub_nonneg.mp h₄⟩

def seed (scale : ℕ+) (z : ℚ) : Interval :=
  let cubic := 1-z+z^2/2-z^3/6
  roundOut ⟨cubic, cubic+z^4/24⟩ scale

theorem seed_sound (scale : ℕ+) {z : ℚ} (hz : 0 ≤ z) : (seed scale z).Mem (Real.exp (-(z:ℝ))) := by
  apply roundOut_mem
  simpa [Mem, p₄, p₃, p₂] using exp_polynomial_bounds (t := (z:ℝ)) (by exact_mod_cast hz)

def gaussianEntry (scale : ℕ+) (z : ℚ) (n : ℕ) := entry scale (seed scale z) (seed scale (2*z)) n

theorem gaussianEntry_sound (scale : ℕ+) {z : ℚ} (hz : 0 ≤ z) (n : ℕ) :
    (gaussianEntry scale z n).sample.Mem (Real.exp (-(z:ℝ) * (n:ℝ)^2)) :=
  (entry_sound scale (seed_sound scale hz)
    (by simpa using seed_sound scale (z:=2*z) (mul_nonneg (by norm_num) hz)) n).1

end GaussianChains.Cert.Nodes
