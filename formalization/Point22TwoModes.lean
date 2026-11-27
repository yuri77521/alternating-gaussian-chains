import Point22Zeros
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-! Convert the two retained spatial harmonics into the actual degree-four
polynomial used in the six-zero obstruction. The coefficient signs are arbitrary. -/
namespace GaussianChains.Point22
open Polynomial Set

noncomputable def twoHarmonics (a b c d e θ : ℝ) :=
  a + b*Real.cos θ + c*Real.sin θ + d*Real.cos (2*θ) + e*Real.sin (2*θ)

private noncomputable def liftedQuartic (a b c d e : ℝ) : Polynomial ℂ :=
  C (((d:ℂ)-e*Complex.I)/2)*X^4 + C (((b:ℂ)-c*Complex.I)/2)*X^3 +
  C (a:ℂ)*X^2 + C (((b:ℂ)+c*Complex.I)/2)*X + C (((d:ℂ)+e*Complex.I)/2)

private theorem cos_on_circle (θ : ℝ) :
    (Real.cos θ : ℂ) = (circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹)/2 := by
  simp [circleMap_zero,Complex.ofReal_cos,Complex.cos,Complex.exp_neg]

private theorem sin_on_circle (θ : ℝ) :
    (Real.sin θ : ℂ) = ((circleMap 0 1 θ)⁻¹ - circleMap 0 1 θ)*Complex.I/2 := by
  simp [circleMap_zero,Complex.ofReal_sin,Complex.sin,Complex.exp_neg]

private theorem liftedQuartic_eval (a b c d e θ : ℝ) :
    (liftedQuartic a b c d e).eval (circleMap 0 1 θ) =
      (circleMap 0 1 θ)^2 * (twoHarmonics a b c d e θ : ℂ) := by
  have hz : circleMap 0 1 θ ≠ 0 := by simp [circleMap_zero, Complex.exp_ne_zero]
  have hd : circleMap 0 1 (2*θ) = (circleMap 0 1 θ)^2 := by
    simpa using (circleMap_zero_pow 2 1 θ).symm
  simp only [liftedQuartic,eval_add,eval_mul,eval_pow,eval_X,eval_C,
    twoHarmonics,Complex.ofReal_add,Complex.ofReal_mul,cos_on_circle,sin_on_circle,hd]
  generalize circleMap 0 1 θ = z at hz ⊢
  field_simp
  <;> ring

theorem no_alternation_two_harmonics (a b c d e : ℝ) (x : Fin 7 → ℝ)
    (hx : StrictMono x) (hlen : x (Fin.last 6)-x 0 ≤ 2*Real.pi) :
    ¬ (∀ j : Fin 6,
      twoHarmonics a b c d e (x j.castSucc)*twoHarmonics a b c d e (x j.succ) < 0) := by
  apply no_alternation_of_degree_four _ _ (liftedQuartic a b c d e) _ (liftedQuartic_eval a b c d e) x hx hlen
  · unfold twoHarmonics; fun_prop
  · unfold liftedQuartic; compute_degree

/-- Arbitrary signed translates of the first two cosine harmonics, including
the signed truncated external potential of the six-site problem. -/
noncomputable def translatedTwoModes {n : ℕ} (phase weight : Fin n → ℝ) (A B θ : ℝ) :=
  ∑ j, weight j * (A*Real.cos (θ-phase j) + B*Real.cos (2*(θ-phase j)))

theorem translatedTwoModes_eq {n : ℕ} (phase weight : Fin n → ℝ) (A B θ : ℝ) :
    translatedTwoModes phase weight A B θ =
      twoHarmonics 0 (∑ j, weight j * A * Real.cos (phase j))
        (∑ j, weight j * A * Real.sin (phase j))
        (∑ j, weight j * B * Real.cos (2*phase j))
        (∑ j, weight j * B * Real.sin (2*phase j)) θ := by
  simp only [translatedTwoModes,twoHarmonics, zero_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_sub,Real.cos_sub,Real.cos_sub]
  ring

theorem no_alternation_translatedTwoModes {n : ℕ} (phase weight : Fin n → ℝ) (A B : ℝ)
    (x : Fin 7 → ℝ) (hx : StrictMono x) (hlen : x (Fin.last 6)-x 0 ≤ 2*Real.pi) :
    ¬ (∀ j : Fin 6,
      translatedTwoModes phase weight A B (x j.castSucc) *
        translatedTwoModes phase weight A B (x j.succ) < 0) := by
  simp_rw [translatedTwoModes_eq]
  exact no_alternation_two_harmonics _ _ _ _ _ x hx hlen

#print axioms no_alternation_translatedTwoModes
end GaussianChains.Point22
