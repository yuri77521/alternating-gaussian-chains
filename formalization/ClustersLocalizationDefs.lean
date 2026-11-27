import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace GaussianChains.Localization
open Real MeasureTheory Set Finset

def osc (n : ℕ) (t : ℝ) : ℂ := Complex.exp ((n*t : ℝ) * Complex.I)

def chartWave (n : ℕ) (i : Fin 4) (t : ℝ) : ℂ :=
  let p := (-1 : ℂ)^n
  match i.val with
  | 0 => -osc n t
  | 1 => -(p * osc n (-t))
  | 2 => p * osc n t
  | _ => osc n (-t)


def arcMass (d : Fin 4 → ℝ → ℝ) : ℝ := ∑ i, ∫ t in 0..π/2, d i t
def arcCost (d : Fin 4 → ℝ → ℝ) : ℝ := ∑ i, ∫ t in 0..π/2, sin t * d i t

/-- Change of the integration-by-parts mode relative to the semicircle.
Multiplication by a constant of modulus one does not change its squared norm. -/
def modeChange (n : ℕ) (d : Fin 4 → ℝ → ℝ) : ℂ :=
  (n : ℝ) • ∑ i, ∫ t in 0..π/2, d i t • chartWave n i t

/-- The normalized integral of the reference semicircle for positive modes. -/
def dipoleMode (n : ℕ) : ℂ := if Even n then 0 else 2 * Complex.I

/-- Fourier integral of an occupation pattern in the four radial charts. -/
def arcMode (n : ℕ) (d : Fin 4 → ℝ → ℝ) : ℂ := dipoleMode n + modeChange n d


end GaussianChains.Localization

