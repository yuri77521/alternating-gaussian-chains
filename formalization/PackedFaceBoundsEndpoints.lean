import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit low-mode estimates for the two endpoint slopes in Theorem 3. -/
namespace GaussianChains.PackedFace

open Real

noncomputable section

theorem cos_floor_small {h : ℝ} (h0 : 0 ≤ h) (h8 : h ≤ 1/8) :
    √2 / 2 ≤ cos (2 * π * h) := by
  rw [← cos_pi_div_four]
  exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos])
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h8) pi_pos.le])

theorem cos_floor_large {h : ℝ} (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) :
    1/2 ≤ cos (2 * π * h) ∧ cos (2 * π * h) ≤ √2 / 2 := by
  rw [← cos_pi_div_three, ← cos_pi_div_four]
  have ha : 2 * π * h ≤ π / 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) pi_pos.le]
  have hb : π / 4 ≤ 2 * π * h := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h8) pi_pos.le]
  exact ⟨cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) (by linarith [pi_pos]) ha,
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hb⟩

/-- Low modes on the small-floor part of the packed face, as polynomials in
`x = cos (2πh)`. -/
theorem small_floor_modes {x : ℝ} (hx : √2 / 2 ≤ x) (hx1 : x ≤ 1) :
    (17/100 : ℝ) < (2*x-1)^2 ∧ |4*x^2-3| ≤ 1 ∧ (8*x^3-6*x-1)^2 < 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have h707 : (707/1000 : ℝ) ≤ x := by
    have : (707/500 : ℝ) ≤ √2 := by nlinarith
    linarith
  have hsq : (1/2 : ℝ) ≤ x^2 := by
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ √2 / 2) hx]
  have hx2 : x^2 ≤ 1 := by nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ x) hx1]
  have hlow : -(61/25 : ℝ) ≤ 8*x^3-6*x-1 := by
    have c : 0 ≤ 8*x^2+8*x*(707/1000)+8*(707/1000:ℝ)^2-6 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h707) c]
  have hupp : 8*x^3-6*x-1 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
      (show 0 ≤ 8*x^2+8*x+2 by nlinarith [sq_nonneg x])]
  refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  · nlinarith [sq_nonneg (2*x-1-414/1000)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hupp) (sub_nonneg.mpr hlow)]

/-- The cubic endpoint is the cosine of the outer displacement. -/
theorem endpoint_cos_cubic (h : ℝ) :
    cos (2*π*(1/2-3*h)) = 3*cos (2*π*h)-4*cos (2*π*h)^3 := by
  rw [show 2*π*(1/2-3*h) = π - 3*(2*π*h) by ring, cos_sub, cos_pi, sin_pi, cos_three_mul]
  ring

theorem large_floor_modes {x : ℝ} (hx : 1/2 ≤ x) (hu : x ≤ √2/2) :
    1 ≤ (4*x^2-3)^2 ∧ 1/2 ≤ 3*x-4*x^3 ∧ 3*x-4*x^3 ≤ 1 ∧
    -3 ≤ 3-12*x^2 ∧ 3-12*x^2 ≤ 0 := by
  have xs : x^2 ≤ 1/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      mul_self_le_mul_self (by linarith : 0 ≤ x) hu]
  have xs' : 1/4 ≤ x^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hx]
  have hx0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_, by linarith, by linarith⟩
  · nlinarith [sq_nonneg (4*x^2-2)]
  · nlinarith [mul_nonneg hx0 (show 0 ≤ 2-4*x^2 by linarith)]
  · nlinarith [mul_nonneg (sq_nonneg (x-1/2)) (show 0 ≤ 4*x+4 by linarith)]

def slopeHead (q x z : ℝ) : ℝ := (2*x-1)^2-4*q^3*(4*x^2-3)^2*z

/-- Total derivative along either endpoint, including the derivative of the
outer cosine `z(x)`. -/
theorem slopeHead_hasDerivAt_x (q x z' : ℝ) (z : ℝ → ℝ) (hz : HasDerivAt z z' x) :
    HasDerivAt (fun t => slopeHead q t (z t))
      (4*(2*x-1) + 64*q^3*x*(3-4*x^2)*z x - 4*q^3*(4*x^2-3)^2*z') x := by
  unfold slopeHead
  convert (((((hasDerivAt_id x).const_mul 2).sub_const 1).pow 2).sub
    (((((((hasDerivAt_id x).pow 2).const_mul 4).sub_const 3).pow 2).const_mul
      (4*q^3)).mul hz)) using 1
  simp
  ring

theorem slopeHead_hasDerivAt_q (q x z : ℝ) :
    HasDerivAt (fun t => slopeHead t x z) (-(12*q^2*(4*x^2-3)^2*z)) q := by
  unfold slopeHead
  convert (hasDerivAt_const q ((2*x-1)^2)).sub
    (((((hasDerivAt_id q).pow 3).const_mul 4).mul_const ((4*x^2-3)^2)).mul_const z)
    using 1
  simp only [id_eq, Nat.cast_ofNat]
  ring

theorem slopeHead_dx_lower {q x z z' : ℝ} (hq : 0 ≤ q) (hx : 1/2 ≤ x)
    (hxx : x^2 ≤ 1/2) (hz : 1/2 ≤ z) (hz' : z' ≤ 0) :
    16*q^3 ≤ 4*(2*x-1)+64*q^3*x*(3-4*x^2)*z-4*q^3*(4*x^2-3)^2*z' := by
  have h1 : 1 ≤ 3-4*x^2 := by linarith
  have h2 : 1/2 ≤ x*(3-4*x^2) := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) (sub_nonneg.mpr h1)]
  have h3 : 1/4 ≤ x*(3-4*x^2)*z := by
    nlinarith [mul_nonneg (show 0 ≤ x*(3-4*x^2) by linarith) (sub_nonneg.mpr hz)]
  nlinarith [mul_nonneg (show 0 ≤ q^3 by positivity) (sub_nonneg.mpr h3),
    mul_nonneg (show 0 ≤ 4*q^3*(4*x^2-3)^2 by positivity) (neg_nonneg.mpr hz')]

theorem slopeHead_qdq_upper {q x z : ℝ} (hq : 0 ≤ q) (hxx : x^2 ≤ 1/2)
    (hz : 1/2 ≤ z) : q * (-(12*q^2*(4*x^2-3)^2*z)) ≤ -6*q^3 := by
  have h1 : 1 ≤ (4*x^2-3)^2 := by nlinarith [sq_nonneg (4*x^2-2)]
  have h2 : 1/2 ≤ (4*x^2-3)^2*z := by
    nlinarith [mul_nonneg (sq_nonneg (4*x^2-3)) (sub_nonneg.mpr hz)]
  nlinarith [mul_nonneg (show 0 ≤ q^3 by positivity) (sub_nonneg.mpr h2)]

/-- At the uniform cell the two endpoints coincide and the entire head of
the slope has the exact value needed for the sign test. -/
theorem slopeHead_uniform (q : ℝ) :
    slopeHead q (1/2) 1 = -16*q^3 ∧
    slopeHead q (1/2) (3*(1/2)-4*(1/2)^3) = -16*q^3 := by
  unfold slopeHead
  constructor <;> ring

/-- Lower bound for the first two modes of the endpoint slope. This is
uniform in the endpoint cosine and applies up to and including `h=1/8`. -/
theorem slopeHead_small_floor {q x z : ℝ} (hq : 0 ≤ q) (hx : √2/2 ≤ x)
    (hx1 : x ≤ 1) (hz : z ≤ 1) : 17/100 - 4*q^3 < slopeHead q x z := by
  obtain ⟨h1,h2,_⟩ := small_floor_modes hx hx1
  have hA : (4*x^2-3)^2 ≤ 1 := by
    rcases abs_le.mp h2 with ⟨ha,hb⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr ha)]
  have hAz : (4*x^2-3)^2*z ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg (4*x^2-3)) (sub_nonneg.mpr hz)]
  unfold slopeHead
  nlinarith [mul_nonneg (show 0 ≤ q^3 by positivity) (sub_nonneg.mpr hAz)]

/-- The outer endpoint as a function of `x = cos(2πh)`. -/
theorem cubic_endpoint_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => 3*t-4*t^3) (3-12*x^2) x := by
  convert ((hasDerivAt_id x).const_mul 3).sub (((hasDerivAt_id x).pow 3).const_mul 4)
    using 1
  simp
  ring

/-- Width derivative in the change of variables used by both critical curves. -/
theorem nome_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ => exp (-(π^2)/u)) (π^2 * exp (-(π^2)/s) / s^2) s := by
  have d := ((hasDerivAt_const s (-(π^2))).div (hasDerivAt_id s) hs.ne').exp
  convert d using 1
  simp
  ring

theorem nome_strictMonoOn :
    StrictMonoOn (fun s : ℝ => exp (-(π^2)/s)) (Set.Ioi 0) := by
  intro s hs t ht hst
  apply Real.exp_lt_exp.mpr
  simp only [neg_div]
  exact neg_lt_neg (div_lt_div_of_pos_left (by positivity) hs hst)

/-- A critical floor strictly decreasing in the nome is strictly decreasing
in the physical width throughout the stated nome range. -/
theorem decreasing_in_width_of_decreasing_in_nome {r : ℝ → ℝ}
    (hr : StrictAntiOn r (Set.Ioc 0 (17/50))) :
    StrictAntiOn (fun s : ℝ => r (exp (-(π^2)/s)))
      {s : ℝ | 0 < s ∧ exp (-(π^2)/s) ≤ 17/50} := by
  intro s hs t ht hst
  exact hr ⟨exp_pos _, hs.2⟩ ⟨exp_pos _, ht.2⟩ (nome_strictMonoOn hs.1 ht.1 hst)

end

end GaussianChains.PackedFace

