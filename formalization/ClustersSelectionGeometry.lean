import ChainGeometry
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A chart for two consecutive odd blocks, with all cyclic inequalities. -/
noncomputable section
open Real
namespace GaussianChains.Clusters

/-- Normalize two angular coordinate charts (at zero and π) to one cell. -/
def joinedBlocks {A B : ℕ} (x : Fin A → ℝ) (y : Fin B → ℝ) (i : Fin (A+B)) : ℝ :=
  Fin.append x (fun j => π+y j) i / (2*π)

def joinedSites (k l : ℕ) (u v : ℕ → ℝ) : Fin ((2*k+1)+(2*l+1)) → ℝ :=
  joinedBlocks (fun i => u i.val) (fun j => v j.val)

theorem joined_eval (k l : ℕ) (u v : ℕ → ℝ) (i : Fin ((2*k+1)+(2*l+1))) :
    joinedSites k l u v i =
      (if i.val < 2*k+1 then u i.val else π+v (i.val-(2*k+1)))/(2*π) := by
  by_cases hi : i.val < 2*k+1
  · rw [if_pos hi]
    let j : Fin (2*k+1) := ⟨i.val,hi⟩
    change Fin.append _ _ (j.castAdd (2*l+1)) / _ = _
    rw [Fin.append_left]
  · rw [if_neg hi]
    let j : Fin (2*l+1) := ⟨i.val-(2*k+1), by omega⟩
    have hj : Fin.natAdd (2*k+1) j = i := by
      apply Fin.ext
      change 2*k+1+(i.val-(2*k+1))=i.val
      omega
    change Fin.append _ _ i / _ = _
    conv_lhs => rw [← hj, Fin.append_right]

/-- Exact angular gap with the internal edges, the cut between blocks, and
the edge through the end of the cell displayed separately. -/
theorem joined_gap (k l : ℕ) (u v : ℕ → ℝ) (i : Fin ((2*k+1)+(2*l+1))) :
    2*π*gap (by omega) (joinedSites k l u v) i =
      if i.val<2*k then u (i.val+1)-u i.val
      else if i.val=2*k then π+v 0-u (2*k)
      else if i.val+1=(2*k+1)+(2*l+1) then π+u 0-v (2*l)
      else v (i.val-(2*k+1)+1)-v (i.val-(2*k+1)) := by
  have hscale (a b : ℝ) : 2*π*(a/(2*π)-b/(2*π)) = a-b := by field_simp [pi_ne_zero]
  by_cases hl : i.val+1=(2*k+1)+(2*l+1)
  · rw [gap_wrap _ _ _ hl,joined_eval,joined_eval,
      if_neg (by omega : ¬i.val<2*k),if_neg (by omega : i.val≠2*k),if_pos hl]
    simp only [Fin.val_mk,if_pos (by omega : 0<2*k+1),if_neg (by omega : ¬i.val < 2*k+1),
      show i.val-(2*k+1)=2*l by omega]
    field_simp [pi_ne_zero]
    <;> ring
  · have hi : i.val+1 < (2*k+1)+(2*l+1) := by omega
    rw [gap_interior _ _ _ hi,joined_eval,joined_eval,hscale]
    simp only [Fin.val_mk,if_neg hl]
    by_cases ha : i.val < 2*k
    · simp [ha,show i.val+1<2*k+1 by omega,show i.val<2*k+1 by omega]
    · by_cases hb : i.val=2*k
      · simp [hb]
      · simp only [if_neg ha,if_neg hb,if_neg (by omega : ¬i.val+1<2*k+1),
          if_neg (by omega : ¬i.val<2*k+1),add_sub_add_left_eq_sub,
          show i.val+1-(2*k+1)=i.val-(2*k+1)+1 by omega]

/-- Both physical blocks remain feasible precisely when these four groups
of inequalities hold. Singleton blocks have no internal inequalities. -/
theorem joinedBlocks_feasible_iff (k l : ℕ) (u v : ℕ → ℝ) (h : ℝ) :
    Feasible (by omega) h (joinedSites k l u v) ↔
      (∀ i < 2*k, 2*π*h ≤ u (i+1)-u i) ∧
      (∀ j < 2*l, 2*π*h ≤ v (j+1)-v j) ∧
      2*π*h ≤ π+v 0-u (2*k) ∧ 2*π*h ≤ π+u 0-v (2*l) := by
  let N := (2*k+1)+(2*l+1)
  have hc : 0 < 2*π := by positivity
  constructor
  · intro hf
    have hb (i : Fin N) := mul_le_mul_of_nonneg_left (hf i) hc.le
    simp_rw [joined_gap] at hb
    refine ⟨fun i hi => ?_,fun j hj => ?_,?_,?_⟩
    · simpa only [Fin.val_mk, if_pos hi] using hb ⟨i,by dsimp [N]; omega⟩
    · let i : Fin N := ⟨2*k+1+j,by dsimp [N]; omega⟩
      have e := hb i
      simpa only [i,Fin.val_mk,if_neg (by omega : ¬2*k+1+j<2*k),
        if_neg (by omega : 2*k+1+j≠2*k),if_neg (by omega : 2*k+1+j+1≠(2*k+1)+(2*l+1)),
        Nat.add_sub_cancel_left] using e
    · simpa using hb ⟨2*k,by dsimp [N]; omega⟩
    · let i : Fin N := ⟨(2*k+1)+2*l,by dsimp [N]; omega⟩
      simpa only [i,Fin.val_mk,if_neg (by omega : ¬2*k+1+2*l<2*k),
        if_neg (by omega : 2*k+1+2*l≠2*k),if_pos (by omega : 2*k+1+2*l+1=(2*k+1)+(2*l+1))]
        using hb i
  · rintro ⟨ha,hb,hc₁,hc₂⟩ i
    apply (le_of_mul_le_mul_left _ hc)
    rw [joined_gap]
    split_ifs with h₁ h₂ h₃
    · exact ha _ h₁
    · exact hc₁
    · exact hc₂
    · exact hb _ (by have := i.isLt; omega)

end GaussianChains.Clusters

