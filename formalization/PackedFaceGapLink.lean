import PackedFaceGeometry
import ChainGeometry
import Mathlib.Tactic.FinCases

/-! The displacement constraint is exactly the six labelled floor inequalities. -/
namespace GaussianChains.PackedFace

theorem labelled_gaps (h t : ℝ) :
    GaussianChains.gap (by decide) (sites h t) =
      ![h,h,1/2-2*h+t,h,h,1/2-2*h-t] := by
  funext i
  fin_cases i <;> norm_num [gap,liftSite,sites,Matrix.cons_val_succ] <;> ring

theorem all_gaps_iff (h t : ℝ) :
    GaussianChains.Feasible (by decide) h (sites h t) ↔ feasible h t := by
  unfold GaussianChains.Feasible
  rw [labelled_gaps,feasible,bound,abs_le]
  constructor
  · intro H
    have hl := H 2
    have hr := H 5
    change h ≤ 1/2-2*h+t at hl
    change h ≤ 1/2-2*h-t at hr
    constructor <;> linarith
  · rintro ⟨hl,hr⟩ i
    fin_cases i <;> simp <;> linarith

end GaussianChains.PackedFace
