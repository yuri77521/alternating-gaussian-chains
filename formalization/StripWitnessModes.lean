import PackedFaceModes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A real off-edge box in the first broad-strip floor band.
For three short alternating dimers the n-th harmonic is at most linear in n. -/
noncomputable section
namespace GaussianChains.Strip

open GaussianChains.PackedFace

/-- The three alternating gaps in this box may vary independently in [0,.074]. -/
def shortDimers (x : Fin 6 → ℝ) : Prop :=
  |x 0 - x 1| ≤ 37/500 ∧ |x 2 - x 3| ≤ 37/500 ∧ |x 4 - x 5| ≤ 37/500

def sixWave (x : Fin 6 → ℝ) (n : ℕ) : ℂ :=
  wave n (x 0) - wave n (x 1) + wave n (x 2) - wave n (x 3) +
    wave n (x 4) - wave n (x 5)

theorem wave_chord_le (n : ℕ) (x y : ℝ) :
    ‖wave n x - wave n y‖ ≤ (2*Real.pi*n)*|x-y| := by
  let f (a : ℝ) := (((2*Real.pi*(n:ℝ)*a : ℝ) : ℂ) * Complex.I)
  have hf : f x = f (x-y) + f y := by
    dsimp [f]
    push_cast
    ring
  change ‖Complex.exp (f x) - Complex.exp (f y)‖ ≤ _
  rw [hf, Complex.exp_add, ← sub_one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(n:ℝ)*(x-y))
  simpa [f, mul_comm Complex.I, Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le] using hb

theorem dimers_mode_bound {x : Fin 6 → ℝ} (hx : shortDimers x) (n : ℕ) :
    ‖sixWave x n‖ ≤ (7/5)*(n : ℝ) := by
  rcases hx with ⟨h0,h2,h4⟩
  have hb (a b : ℝ) (hab : |a-b| ≤ 37/500) :
      ‖wave n a - wave n b‖ ≤ (2*Real.pi*(37/500))*(n : ℝ) := by
    calc
      _ ≤ (2*Real.pi*(n:ℝ))*|a-b| := wave_chord_le n a b
      _ ≤ (2*Real.pi*(n:ℝ))*(37/500) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
      _ = _ := by ring
  rw [sixWave, show wave n (x 0) - wave n (x 1) + wave n (x 2) - wave n (x 3) +
       wave n (x 4) - wave n (x 5) =
       ((wave n (x 0)-wave n (x 1))+(wave n (x 2)-wave n (x 3)))+
       (wave n (x 4)-wave n (x 5)) by ring]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hπ : 3*(2*Real.pi*(37/500)) ≤ 7/5 := by linarith [Real.pi_lt_d4]
  linarith only [hb _ _ h0, hb _ _ h2, hb _ _ h4,
    mul_le_mul_of_nonneg_right hπ (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Centered packed triples retain a strictly larger first mode on the whole band. -/
theorem centered_mode_lower {h : ℝ} (hl : 0 ≤ h) (hr : h ≤ 9/125) :
    (5/2 : ℝ) ≤ 4*(2*Real.cos (2*Real.pi*h)-1)^2 := by
  have ha : 0 ≤ 2*Real.pi*h := by positivity
  have hb : 2*Real.pi*h ≤ 227/500 := by
    calc
      _ ≤ 2*(3.15:ℝ)*(9/125) := by gcongr; exact Real.pi_lt_d2.le
      _ ≤ _ := by norm_num
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*h)
  have hd := pow_le_pow_left₀ ha hb 2
  have he : (793/1000:ℝ) ≤ 2*Real.cos (2*Real.pi*h)-1 := by nlinarith only [hc,hd]
  nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 793/1000) he 2]

end GaussianChains.Strip
