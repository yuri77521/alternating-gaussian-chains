import ChainEnergy
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Spatial differentiation of the image sums used by the Gaussian certificates.
The majorant is valid uniformly on a bounded interval and for every positive width. -/

noncomputable section
namespace GaussianChains.ImageCalculus

open Polynomial Set

/-- A polynomial is bounded by any growing Gaussian, with a constant depending
on the polynomial and the Gaussian exponent. -/
private theorem polynomial_bound (p : ℝ[X]) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |p.eval t| ≤ C * Real.exp (δ*t^2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C, hC, hp⟩ := hp
    obtain ⟨D, hD, hq⟩ := hq
    refine ⟨C+D, add_nonneg hC hD, fun t => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hp t) (hq t))
  | monomial n c =>
    refine ⟨|c| * Real.exp ((n:ℝ)^2/(4*δ)), by positivity, fun t => ?_⟩
    have hs := sq_nonneg (2*δ*|t|-(n:ℝ))
    simp only [sub_sq, mul_pow, sq_abs] at hs
    have hbudget : (n:ℝ)*|t|-δ*t^2 ≤ (n:ℝ)^2/(4*δ) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith only [hs]
    have ht : |t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
    rw [Polynomial.eval_monomial, abs_mul, abs_pow, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      |t|^n ≤ (Real.exp |t|)^n := pow_le_pow_left₀ (abs_nonneg _) ht _
      _ = Real.exp ((n:ℝ)*|t|) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hbudget])

/-- One periodized image with polynomial multiplier. -/
def imageTerm (s : ℝ) (p : ℝ[X]) (k : ℤ) (x : ℝ) : ℝ :=
  p.eval (x+k) * Real.exp (-s*(x+k)^2)

/-- Uniform absolute majorant for one derivative order on a bounded interval. -/
theorem summable_envelope {s A : ℝ} (hs : 0 < s) (p : ℝ[X]) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ k x, |x| ≤ A → |imageTerm s p k x| ≤ u k := by
  obtain ⟨C, hC, hpoly⟩ := polynomial_bound p (δ:=s/2) (by positivity)
  let K := C * Real.exp (s/2*A^2)
  let u := fun k : ℤ => K * Real.exp (-(s/4) * (k:ℝ)^2)
  refine ⟨u, ?_, ?_⟩
  · simpa [u] using (GaussianChains.kernel_summable (s/4) 0 (by positivity)).mul_left K
  · intro k x hx
    have hx2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at hx2
    rw [imageTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (C * Real.exp (s/2*(x+k)^2)) * Real.exp (-s*(x+k)^2) :=
        mul_le_mul_of_nonneg_right (hpoly (x+k)) (Real.exp_nonneg _)
      _ = C * Real.exp (-(s/2)*(x+k)^2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ u k := by
        dsimp [u, K]
        rw [mul_assoc, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        linarith only [mul_nonneg hs.le (sq_nonneg (2*x+(k:ℝ))),
          mul_le_mul_of_nonneg_left hx2 hs.le]

/-- Periodized polynomial-weighted Gaussian. -/
def periodized (s : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ := ∑' k : ℤ, imageTerm s p k x

/-- The ordinary product rule applied before summation. -/
def next (s : ℝ) (p : ℝ[X]) : ℝ[X] := p.derivative + C (-2*s)*X*p

theorem imageTerm_derivative (s : ℝ) (p : ℝ[X]) (k : ℤ) (x : ℝ) :
    HasDerivAt (imageTerm s p k) (imageTerm s (next s p) k x) x := by
  have hd := (hasDerivAt_id x).add_const (k:ℝ)
  have h := ((p.hasDerivAt (x+k)).comp x hd).mul (((hd.fun_pow 2).const_mul (-s)).exp)
  convert h using 1
  simp [imageTerm, next]
  ring

/-- Pointwise summability in all polynomial orders. -/
theorem imageTerm_summable {s : ℝ} (hs : 0 < s) (p : ℝ[X]) (x : ℝ) :
    Summable fun k => imageTerm s p k x := by
  obtain ⟨u, hu, hdom⟩ := summable_envelope (A:=|x|) hs p
  exact Summable.of_norm_bounded hu (fun k => by simpa only [Real.norm_eq_abs] using hdom k x le_rfl)

/-- For each order the integer sum really differentiates to the sum with the
next multiplier. This holds for all displacements, including cell endpoints. -/
theorem periodized_derivative {s : ℝ} (hs : 0 < s) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (periodized s p) (periodized s (next s p) x) x := by
  let A := |x|+1
  have hx : x ∈ Ioo (-A) A := abs_lt.mp (by dsimp [A]; linarith)
  obtain ⟨u, hu, hdom⟩ := summable_envelope (A:=A) hs (next s p)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => imageTerm_derivative s p k y)
    (fun k y hy => by simpa only [Real.norm_eq_abs] using hdom k y (abs_lt.mpr hy).le)
    hx (imageTerm_summable hs p x) hx

theorem kernel_periodized (s : ℝ) : GaussianChains.kernel s = periodized s 1 := by
  funext x
  simp [GaussianChains.kernel, periodized, imageTerm]

/-- All spatial derivative series of the Gaussian image kernel. -/
theorem kernel_iterated_deriv {s : ℝ} (hs : 0 < s) (n : ℕ) :
    deriv^[n] (GaussianChains.kernel s) = periodized s ((next s)^[n] 1) := by
  induction n with
  | zero => exact kernel_periodized s
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact funext (fun x => (periodized_derivative hs _ x).deriv)

end GaussianChains.ImageCalculus
