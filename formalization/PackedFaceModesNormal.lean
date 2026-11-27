import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A normal limit of holomorphic polynomials in the two complex parameters.
The Schwarz estimate controls both partial derivatives, even at a zero of a summand. -/
namespace GaussianChains.PackedFace
open Metric Set Filter
open scoped Topology

/-- On a neighborhood of the two-parameter base point, an ordinary summable
bound on the modes implies continuous complex Fréchet differentiability of the
sum. The proof uses the larger ball for the Schwarz derivative estimate. -/
theorem joint_contDiffAt_tsum {f : ℕ → (ℂ × ℂ) → ℂ} {v : ℕ → ℝ} {a : ℂ × ℂ}
    (hf : ∀ n, ContDiff ℂ 1 (f n)) (hv : Summable v)
    (hb : ∀ᶠ p in 𝓝 a, ∀ n, ‖f n p‖ ≤ v n) :
    ContDiffAt ℂ 1 (fun p => ∑' n, f n p) a := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hb
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hbound (n : ℕ) (p : ℂ × ℂ) (hp : p ∈ ball a R) : ‖f n p‖ ≤ v n :=
    hball hp n
  have hdiff (n : ℕ) := (hf n).differentiable one_ne_zero
  have hder (n : ℕ) (p : ℂ × ℂ) (hp : p ∈ ball a r) :
      ‖fderiv ℂ (f n) p‖ ≤ (2/r)*v n := by
    have hle : MapsTo (f n) (ball p r) (closedBall (f n p) (2*v n)) := by
      intro x hx
      have hx' : x ∈ ball a R := by
        have ht := dist_triangle x p a
        change dist x p < r at hx
        change dist p a < r at hp
        change dist x a < R
        dsimp [r] at hx hp
        linarith
      have hp' := hbound n p (ball_subset_ball hrR.le hp)
      change dist (f n x) (f n p) ≤ 2*v n
      calc
        _ ≤ ‖f n x‖ + ‖f n p‖ := dist_le_norm_add_norm _ _
        _ ≤ _ := by linarith [hbound n x hx']
    exact (Complex.norm_fderiv_le_div_of_mapsTo_ball (hdiff n).differentiableOn hle hr).trans_eq
      (by ring)
  have hu := hv.mul_left (2/r)
  have hconv : Summable (fun n => f n a) :=
    Summable.of_norm_bounded hv fun n => hbound n a (mem_ball_self hR)
  rw [contDiffAt_one_iff]
  refine ⟨fun p => ∑' n, fderiv ℂ (f n) p, ball a r, ball_mem_nhds a hr, ?_, ?_⟩
  · exact continuousOn_tsum (fun n => ((hf n).continuous_fderiv one_ne_zero).continuousOn) hu hder
  · intro p hp
    exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball a r).isPreconnected
      (fun n z _ => (hdiff n z).hasFDerivAt) hder (mem_ball_self hr) hconv hp

end GaussianChains.PackedFace

