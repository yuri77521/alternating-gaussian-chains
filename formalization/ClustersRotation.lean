import ChainFourier
import ChainMinimum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Rotating a labelled configuration to align its first angular moment.
Coordinates are periodic lifts; a translation across the chosen cut still
preserves every cyclic gap. -/
noncomputable section
namespace GaussianChains
open Real

theorem gap_sub_const {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (a : ℝ) (i : Fin N) :
    gap hN (fun j => x j - a) i = gap hN x i := by
  unfold gap liftSite
  ring

theorem groundState_sub_const_iff {N : ℕ} (hN : 0 < N) (h s : ℝ) (x : Fin N → ℝ)
    (a : ℝ) :
    IsGroundState hN h s (fun i => x i - a) ↔ IsGroundState hN h s x := by
  simp only [IsGroundState, Feasible, gap_sub_const, imageEnergy_sub_const]

/-- The Fourier amplitude acquires precisely the translation phase. -/
theorem structureFactor_sub_const {N : ℕ} (x : Fin N → ℝ) (a : ℝ) (n : ℕ) :
    structureFactor (fun j => x j - a) n =
      structureFactor x n * Complex.exp (-((2 * π * (n : ℝ) * a : ℝ) : ℂ) * Complex.I) := by
  unfold structureFactor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc (charge j : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A rotation preserves all Fourier norms, also when the mode vanishes. -/
theorem norm_structureFactor_sub_const {N : ℕ} (x : Fin N → ℝ) (a : ℝ) (n : ℕ) :
    ‖structureFactor (fun j => x j - a) n‖ = ‖structureFactor x n‖ := by
  rw [structureFactor_sub_const, norm_mul,
      ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Choose the translation from the complex argument. This formula also works at
zero amplitude: the convention arg(0)=0 leaves the zero mode aligned. -/
def alignmentShift {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (structureFactor x 1).arg / (2*π)

theorem structureFactor_align {N : ℕ} (x : Fin N → ℝ) :
    structureFactor (fun i => x i - alignmentShift x) 1 = (‖structureFactor x 1‖ : ℂ) := by
  let z := structureFactor x 1
  have hp : 2*π*(1:ℝ)*(z.arg/(2*π)) = z.arg := by field_simp [Real.pi_ne_zero]
  rw [structureFactor_sub_const]
  simp only [Nat.cast_one, alignmentShift]
  change z * Complex.exp (-(↑(2*π*(1:ℝ)*(z.arg/(2*π))) : ℂ)*Complex.I) = (‖z‖ : ℂ)
  rw [hp, neg_mul, Complex.exp_neg, ← div_eq_mul_inv]
  apply (div_eq_iff (Complex.exp_ne_zero _)).2
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- The aligned representative lies in the same feasible translation orbit,
has the same energy, and has real nonnegative first structure factor. -/
theorem exists_first_mode_aligned {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (h s : ℝ)
    (hx : Feasible hN h x) :
    ∃ a : ℝ, Feasible hN h (fun i => x i - a) ∧
      imageEnergy s (fun i => x i - a) = imageEnergy s x ∧
      structureFactor (fun i => x i - a) 1 = (‖structureFactor x 1‖ : ℂ) ∧
      ∀ n, ‖structureFactor (fun i => x i - a) n‖ = ‖structureFactor x n‖ := by
  refine ⟨alignmentShift x, fun i => ?_, imageEnergy_sub_const _ _ _,
    structureFactor_align _, fun n => norm_structureFactor_sub_const _ _ _⟩
  simpa only [gap_sub_const] using hx i

#print axioms exists_first_mode_aligned

end GaussianChains
