import ChainGeometry
import PackedFaceGeometry
import StripGeometry
import StripSupports
import Mathlib.Tactic.FinCases

/-! Connecting opposite-gap support to the closed packed face in the actual
unit-period coordinates. A slack coordinate that becomes zero is treated with
its new support, including a single slack coordinate. -/
noncomputable section
namespace GaussianChains.Strip

open GaussianChains.PackedFace

theorem physical_gaps_in_simplex {h : ℝ} {x : Fin 6 → ℝ} (hx : Feasible (by decide) h x) :
    gapVector h (gap (by decide) x) := ⟨hx, sum_gap _ _⟩

theorem physical_uniform_endpoint {x : Fin 6 → ℝ} (hx : Feasible (by decide) (1/6) x) :
    ∀ i, gap (by decide) x i = 1/6 := uniform_endpoint (physical_gaps_in_simplex hx)

/-- Four specified contacts force exactly the six positions of (8), up to
translation. The two remaining gap inequalities give both closed endpoints. -/
theorem closed_contacts_are_face {h : ℝ} {x : Fin 6 → ℝ} (hx : Feasible (by decide) h x)
    (hc : ∀ i : Fin 5, i ≠ 2 → gap (by decide) x i.castSucc = h) :
    ∃ t : ℝ, feasible h t ∧ ∀ i, x i = x 0 + sites h t i := by
  let t := x 3-x 0-1/2
  have gapAt (i : Fin 5) := gap_interior (by decide : 0 < 6) x i.castSucc
    (show i.val+1 < 6 by omega)
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  rw [gapAt] at h0 h1 h3 h4
  change x 1-x 0 = h at h0
  change x 2-x 1 = h at h1
  change x 4-x 3 = h at h3
  change x 5-x 4 = h at h4
  have hm := hx 2
  rw [gap_interior _ _ _ (by decide)] at hm
  change h ≤ x 3-x 2 at hm
  have hw := hx 5
  rw [gap_wrap _ _ _ (by decide)] at hw
  change h ≤ x 0+1-x 5 at hw
  refine ⟨t, ?_, ?_⟩
  · rw [feasible_iff_outer_gaps]
    change h ≤ 1/2+t-2*h ∧ h ≤ 1+0-(1/2+t+2*h)
    dsimp [t]
    constructor <;> linarith
  · intro i
    fin_cases i <;> simp [sites,t] <;> linarith

theorem active_support_face {h : ℝ} (hh : h < 1/6) {x : Fin 6 → ℝ}
    (hx : Feasible (by decide) h x)
    (he : let u := slack h (gap (by decide) x)
          activeSupport u = ∅ ∨ activeSupport u = {2}) :
    ∃ t : ℝ, feasible h t ∧ ∀ i, x i = x 0 + sites h t i := by
  let g := gap (by decide : 0 < 6) x
  have hu := slack_simplex hh (physical_gaps_in_simplex hx)
  have hz := (closedEdge_iff (slack h g) hu.1).mp he
  apply closed_contacts_are_face hx
  intro i hi
  have hpack := congrFun (pack_slack hh g) i.castSucc
  change h + (1-6*h)*slack h g i.castSucc = g i.castSucc at hpack
  rw [hz i hi,mul_zero,add_zero] at hpack
  exact hpack.symm

end GaussianChains.Strip
