import CertTree
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Necessary conditions underlying transfer leaves in the two simplex checkers. -/
namespace GaussianChains.Cert
open Filter Topology

/-- Any two-sided local score maximum has zero transfer slope and nonpositive
transfer curvature. Only continuity of the score at the testing point is needed
when using mathlib's total derivative. -/
theorem necessary_transfer {f : ℝ → ℝ} {t : ℝ} (hm : IsLocalMax f t) (hc : ContinuousAt f t) :
    deriv f t = 0 ∧ deriv (deriv f) t ≤ 0 := by
  refine ⟨hm.deriv_eq_zero, ?_⟩
  by_contra! hp
  have hn := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hm, hn] with x hu hl
    exact le_antisymm hu hl
  have hh := he.deriv.deriv_eq
  simp at hh
  linarith

/-- A two-sided feasible path through a global maximum induces the local
maximum required by the transfer tests. The path may leave the canonical
coordinate chamber (e.g. a tied largest gap) while remaining physically feasible. -/
theorem transfer_conditions {X : Type*} {feasible : Set X} {score : X → ℝ}
    {x : X} {p : ℝ → X} {t : ℝ} (hmax : ∀ y ∈ feasible, score y ≤ score x)
    (hx : p t = x) (hpath : ∀ᶠ u in 𝓝 t, p u ∈ feasible)
    (hc : ContinuousAt (score ∘ p) t) :
    deriv (score ∘ p) t = 0 ∧ deriv (deriv (score ∘ p)) t ≤ 0 := by
  apply necessary_transfer _ hc
  filter_upwards [hpath] with u hu
  change score (p u) ≤ score (p t)
  rw [hx]
  exact hmax _ hu

end GaussianChains.Cert
