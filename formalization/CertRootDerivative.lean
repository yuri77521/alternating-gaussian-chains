import CertTreeKernelDeriv
import CertRootTail

/-! At the isolated width, the certified image series are the actual first
and second derivatives on the entire real line. -/
noncomputable section
namespace GaussianChains.Root22
open GaussianChains.ImageCalculus

def secondImage (u : ℝ) : ℝ := (1936*u^2-44)*Real.exp (-22*u^2)

def curvatureSum (x : ℝ) : ℝ := ∑' k : ℤ, secondImage (x+k)

private theorem first_term (x : ℝ) (k : ℤ) : imageTerm 22 (next 22 1) k x = term x k := by
  simp [imageTerm, next, term, image] <;> ring_nf <;> simp

private theorem first_series : periodized 22 (next 22 1) = derivKernel := by
  funext x
  exact tsum_congr (first_term x)

theorem derivKernel_summable (x : ℝ) : Summable (term x) :=
  (imageTerm_summable (s := 22) (by norm_num) (next 22 1) x).congr (first_term x)

private theorem second_series : periodized 22 (next 22 (next 22 1)) = curvatureSum := by
  funext x
  unfold periodized curvatureSum
  apply tsum_congr
  intro k
  simp [imageTerm, next, secondImage, Polynomial.derivative_mul] <;> ring

theorem hasDerivAt_kernel22 (x : ℝ) : HasDerivAt (GaussianChains.kernel 22) (derivKernel x) x := by
  rw [kernel_periodized, ← first_series]
  exact periodized_derivative (by norm_num) 1 x

theorem hasDerivAt_derivKernel (x : ℝ) : HasDerivAt derivKernel (curvatureSum x) x := by
  rw [← first_series, ← second_series]
  exact periodized_derivative (by norm_num) _ x

theorem curvatureSum_eq_deriv2 (x : ℝ) :
    curvatureSum x = deriv (deriv (GaussianChains.kernel 22)) x := by
  rw [show deriv (GaussianChains.kernel 22) = derivKernel from funext (fun y => (hasDerivAt_kernel22 y).deriv)]
  exact (hasDerivAt_derivKernel x).deriv.symm

end GaussianChains.Root22

