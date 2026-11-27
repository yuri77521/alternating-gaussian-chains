import CertTreeGrid
import CertTreeRanges
import CertTreeFourierCaps
import CertTreeInterpolation

/-! The strip's sampled Gaussian table as a real-space enclosure on the full
displacement interval queried by each continuous box. Width perturbation is
applied separately, after evaluating this reference kernel. -/
namespace GaussianChains.Cert.Tables
open GaussianChains.ImageBounds GaussianChains.ImageCalculus GaussianChains.FourierBounds

def stripCap : Order → ℚ
  | .value => 4
  | .first => 20
  | .second => 150

def stripNode (s : ℚ) (j : Order) : ℕ → Interval :=
  gridNode (10^32) (10^9) 8192 s j

def stripRange (s : ℚ) (j : Order) (left right : ℚ) : Interval :=
  spatialRange 8192 (10^9) (stripCap j) (stripNode s j) left right

theorem kernel_differentiable_order {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Differentiable ℝ (deriv^[n] (kernel s)) := by
  rw [kernel_iterated_deriv hs]
  exact fun x => (periodized_derivative hs _ x).differentiableAt

theorem stripRange_sound {s : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9) (j : Order)
    {left right : ℚ} (hl : 0 ≤ left) (hr : right ≤ 1) {x : ℝ}
    (hx : (left:ℝ) ≤ x ∧ x ≤ (right:ℝ)) :
    (stripRange s j left right).Mem ((deriv^[orderIndex j] (kernel (s:ℝ))) x) := by
  have hs' : (s:ℝ) ∈ Set.Icc (8:ℝ) 9 := ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
  have hs0 : 0 < (s:ℝ) := by linarith [hs'.1]
  apply spatialRange_mem (cap:=stripCap j) (by cases j <;> norm_num [stripCap])
    (kernel_differentiable_order hs0 _) _ _ _ (fun p hp => gridNode_strip_sound _ _ hs j hp) hl hr hx
  intro y
  obtain ⟨h₁,h₂,h₃⟩ := strip_derivative_caps hs' y
  cases j with
  | value => simpa [orderIndex,stripCap] using h₁.le
  | first => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₂.le
  | second => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₃.le

end GaussianChains.Cert.Tables
