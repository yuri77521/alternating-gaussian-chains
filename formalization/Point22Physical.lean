import Point22Orbits
import ChainSymmetry
import ChainCompact

/-! Connect the cut-mask and orbit computation to the physical labels,
ordered lifts and periodic gaps of the general model. -/

namespace GaussianChains.Point22

private theorem Npos : 0 < 6 := by decide

theorem six_gap_eq (x : Fin 6 → ℝ) : gap Npos x = cyclicGap x := by
  funext i
  by_cases he : i = 5
  · subst i
    rw [gap_wrap Npos x (5:Fin 6) (by decide)]
    change x 0 + 1 - x 5 = x 0 - x 5 + 1
    ring
  · have hin : i.val+1 < 6 :=
      (by decide : ∀ i : Fin 6, i ≠ 5 → i.val+1 < 6) i he
    rw [gap_interior _ _ _ hin]
    simp only [cyclicGap, if_neg he, add_zero]
    have hag : (⟨i.val+1,hin⟩ : Fin 6) = i+1 :=
      (by decide : ∀ (i : Fin 6) (hi : i.val+1 < 6), (⟨i.val+1,hi⟩ : Fin 6) = i+1) i hin
    rw [hag]
theorem physical_support_exhaustion (x : Fin 6 → ℝ) :
    (words.filter (matchesWord (actualCuts (1/1000) (gap Npos x)))).length = 1 :=
  actual_word_unique _ (sum_gap Npos x)

theorem physical_sites_gaps (h R : ℝ) : gap Npos (sites h R) = gapWord h R := by
  rw [six_gap_eq, sites_gaps]

theorem physical_sites_feasible (h R : ℝ) (h₁ : 2*h < R) (h₂ : R < 1/2-h) :
    Feasible Npos h (sites h R) := by
  intro i
  rw [show gap Npos (sites h R) i = _ from congrFun (physical_sites_gaps h R) i]
  exact (feasible_gapWord h R h₁ h₂).1 i

private theorem six_gap_eq_iff (x y : Fin 6 → ℝ) :
    gap Npos x = gap Npos y ↔ ∃ c : ℝ, ∀ i, y i = x i+c := by
  constructor
  · intro hg
    refine ⟨y 0-x 0,?_⟩
    intro i
    have hy := sitesOfGaps_gap Npos y i
    rw [← hg, sitesOfGaps_gap] at hy
    change x i - x 0 = y i - y 0 at hy
    linarith
  · rintro ⟨c,hc⟩
    rw [six_gap_eq x,six_gap_eq y]
    funext i
    simp only [cyclicGap,hc]
    ring
noncomputable def transformed (x : Fin 6 → ℝ) (k : Fin 6) (rev : Bool) : Fin 6 → ℝ :=
  if rev then reflectLifts Npos (shiftLifts Npos x k) else shiftLifts Npos x k

theorem transformed_gap (x : Fin 6 → ℝ) (k i : Fin 6) (rev : Bool) :
    gap Npos (transformed x k rev) i = gap Npos x (edgeIndex k rev i) := by
  cases rev <;> simp [transformed, gap_shiftLifts, gap_reflectLifts, edgeIndex]
  congr 1
  exact (by decide : ∀ i k : Fin 6, i.rev+k = k-1-i) i k

/-- Physical species-preserving relation, including arbitrary rotations on
the circle (translations of all the lifts) and reflection. -/
def SameSpeciesCells (x y : Fin 6 → ℝ) : Prop :=
  ∃ k : Fin 6, k.val % 2 = 0 ∧ ∃ rev : Bool, ∃ c : ℝ, ∀ i, y i = transformed x k rev i + c

theorem physical_orbits_iff_gaps (x y : Fin 6 → ℝ) :
    SameSpeciesCells x y ↔ SameSpecies (gap Npos x) (gap Npos y) := by
  constructor
  · rintro ⟨k,hk,rev,c,hy⟩
    have he := (six_gap_eq_iff _ _).mpr ⟨c,hy⟩
    exact ⟨k,hk,rev,fun i => (congrFun he i).symm.trans (transformed_gap x k i rev)⟩
  · rintro ⟨k,hk,rev,h⟩
    have he : gap Npos (transformed x k rev) = gap Npos y := by
      funext i
      exact (transformed_gap x k i rev).trans (h i).symm
    exact ⟨k,hk,rev,(six_gap_eq_iff _ _).mp he⟩

theorem two_species_orbits (h R : ℝ) (h₁ : 2*h < R) (h₂ : R < 1/2-h)
    (k l : Fin 6) :
    SameSpeciesCells (shiftLifts Npos (sites h R) k) (shiftLifts Npos (sites h R) l) ↔
      k.val % 2 = l.val % 2 := by
  rw [physical_orbits_iff_gaps]
  have hf (j : Fin 6) : gap Npos (shiftLifts Npos (sites h R) j) = rotate (gapWord h R) j := by
    funext i
    rw [gap_shiftLifts, physical_sites_gaps]
    rfl
  rw [hf, hf, shape_orbits_iff h R h₁ h₂]

/-- Charge of the three consecutive labels of the unique triple after recutting. -/
theorem triple_charge (k : Fin 6) :
    charge (-k) + charge (1-k) + charge (2-k) =
      if k.val % 2 = 0 then (1:ℝ) else -1 := by
  have h : ∀ j : Fin 6, (-1:ℤ)^(-j).val + (-1:ℤ)^(1-j).val + (-1:ℤ)^(2-j).val =
        (if j.val % 2 = 0 then (1:ℤ) else -1) := by decide
  unfold charge
  split_ifs with he
  · have H := h k
    rw [if_pos he] at H
    exact_mod_cast H
  · have H := h k
    rw [if_neg he] at H
    exact_mod_cast H

end GaussianChains.Point22
