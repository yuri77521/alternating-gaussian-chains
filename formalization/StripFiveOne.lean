import StripFiveOneComparison
import StripFiveOneModes
import ChainSymmetry
import PackedFaceGapLink
import Mathlib.Analysis.Real.Pi.Bounds

/-! The small-floor exclusion of every 5+1 placement in each physical strip.
Four cyclic contacts suffice regardless of whether either remaining gap is slack. -/
noncomputable section
namespace GaussianChains.Strip
open Real PackedFace

private theorem energy_mass {s : ℝ} (hs : 0 < s) (x : Fin 6 → ℝ) (F : ℕ → ℝ)
    (hx : ∀ n, ‖structureFactor x n‖^2 = F n) :
    imageEnergy s x = 1 - (2*sqrt (π/s)/6*exp (-(π^2)/s))*normalizedMass (exp (-(π^2)/s)) F := by
  rw [imageEnergy_fourier 3 hs, normalizedMass]
  let q := exp (-(π^2)/s)
  have hp (n : ℕ) : q^((n+1)^2) = q*q^((n+1)^2-1) := by
    rw [← pow_succ',Nat.sub_add_cancel (show 1 ≤ (n+1)^2 from pow_pos (Nat.succ_pos n) 2)]
  change 1-(2*sqrt (π/s)/6)*(∑' n : ℕ, q^((n+1)^2)*‖structureFactor x (n+1)‖^2) =
    1-(2*sqrt (π/s)/6*q)*(∑' n : ℕ, q^((n+1)^2-1)*F (n+1))
  simp_rw [hx,hp,mul_assoc,tsum_mul_left] <;> ring

theorem energy_lt_of_split_mass {s h t : ℝ} (hs : 0 < s)
    (hm : normalizedMass (exp (-(π^2)/s)) (fivePower (2*π*h) (2*π*t)) <
      normalizedMass (exp (-(π^2)/s)) (triplePower (2*π*h))) :
    imageEnergy s (sites h 0) < imageEnergy s (fiveSites h t) := by
  rw [energy_mass hs _ _ (fun n => structureFactor_triples_sq n h),
    energy_mass hs _ _ (fun n => structureFactor_fiveSites_sq n h t)]
  exact sub_lt_sub_left (mul_lt_mul_of_pos_left hm (by positivity)) _

theorem broad_five_one_strict {s h : ℝ} (h8 : 8 ≤ s) (h9 : s ≤ 9)
    (hh : 0 < h) (h7 : h ≤ 7/100) (t : ℝ) :
    imageEnergy s (sites h 0) < imageEnergy s (fiveSites h t) := by
  have hs : 0 < s := by linarith
  have he : 2*π*h ≤ 44/100 := by
    calc _ ≤ 2*(3.1416:ℝ)*(7/100) := by gcongr; exact pi_lt_d4.le
         _ ≤ _ := by norm_num
  apply energy_lt_of_split_mass hs
  exact small_angle_mass_lt (exp_pos _).le (broad_nome hs h9).le (by positivity) he
    (broad_tail_constants h8 h9).2.2.2 _

theorem narrow_five_one_strict {s h : ℝ} (h799 : 799/100 ≤ s) (h801 : s ≤ 801/100)
    (hh : 0 < h) (h10 : h ≤ 1/10) (t : ℝ) :
    imageEnergy s (sites h 0) < imageEnergy s (fiveSites h t) := by
  have hs : 0 < s := by linarith
  let q := exp (-(π^2)/s)
  have hq : 0 < q := exp_pos _
  have hqn : q < 292/1000 := narrow_nome hs h801
  have hc := narrow_tail_constants h799 h801
  have he : 2*π*h ≤ π/5 := by nlinarith only [mul_le_mul_of_nonneg_left h10 pi_pos.le]
  apply energy_lt_of_split_mass hs
  rcases le_total (2*π*h) (40/100) with hsmall | hlarge
  · exact small_angle_mass_lt hq.le (by linarith) (by positivity) (by linarith)
      (lt_trans hc.2.2.2 (by norm_num)) _
  · exact large_angle_mass_lt hq.le (by linarith) hlarge he hc.1 _

/-- Intrinsic cyclic statement of the excluded contact pattern. -/
def FourContacts (h : ℝ) (x : Fin 6 → ℝ) : Prop :=
  ∃ i : Fin 6, ∀ j : Fin 4, gap (by decide) x (j.castLE (by decide : 4 ≤ 6)+i) = h

theorem fourContacts_energy {h : ℝ} {x : Fin 6 → ℝ} (hx : FourContacts h x) (s : ℝ) :
    ∃ t : ℝ, imageEnergy s x = imageEnergy s (fiveSites h t) := by
  obtain ⟨i,hi⟩ := hx
  let y := shiftLifts (by decide) x i
  have hy (j : Fin 4) : gap (by decide) y (j.castLE (by decide : 4 ≤ 6)) = h := by
    rw [gap_shiftLifts]; exact hi j
  have hstep (j : Fin 4) :
      y ⟨j.val+1, by omega⟩ - y ⟨j.val, by omega⟩ = h := by
    have hh := hy j
    rw [gap_interior _ _ _ (by change j.val + 1 < 6; omega)] at hh
    exact hh
  have h₀ : y 1-y 0 = h := hstep 0
  have h₁ : y 2-y 1 = h := hstep 1
  have h₂ : y 3-y 2 = h := hstep 2
  have h₃ : y 4-y 3 = h := hstep 3
  let t := y 5 - y 2 - 1/2
  have he : y = fun j => fiveSites h t j + y 2 := by
    rw [fiveSites_coordinates]
    funext j
    fin_cases j <;> simp [Matrix.cons_val, t] <;> linarith
  refine ⟨t, ?_⟩
  calc
    imageEnergy s x = imageEnergy s y := (imageEnergy_shiftLifts (by decide) (by decide) s x i).symm
    _ = imageEnergy s (fun j => fiveSites h t j + y 2) := congrArg (imageEnergy s) he
    _ = imageEnergy s (fiveSites h t) := imageEnergy_translate _ _ _

theorem fourContacts_excluded {s h : ℝ} (hh : 0 < h) (x : Fin 6 → ℝ)
    (hs : (8 ≤ s ∧ s ≤ 9 ∧ h ≤ 7/100) ∨ (799/100 ≤ s ∧ s ≤ 801/100 ∧ h ≤ 1/10))
    (hx : FourContacts h x) : imageEnergy s (sites h 0) < imageEnergy s x := by
  obtain ⟨t,ht⟩ := fourContacts_energy hx s
  rw [ht]
  rcases hs with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · exact broad_five_one_strict ha hb hh hc t
  · exact narrow_five_one_strict ha hb hh hc t

theorem minimizing_cell_has_no_four_contacts {s h : ℝ} (hh : 0 < h) (x : Fin 6 → ℝ)
    (hs : (8 ≤ s ∧ s ≤ 9 ∧ h ≤ 7/100) ∨ (799/100 ≤ s ∧ s ≤ 801/100 ∧ h ≤ 1/10))
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y) :
    ¬ FourContacts h x := by
  intro hc
  have h10 : h ≤ 1/10 := by
    rcases hs with ⟨_,_,hb⟩ | ⟨_,_,hb⟩ <;> linarith
  have hy : Feasible (by decide) h (sites h 0) := by
    rw [all_gaps_iff, feasible, bound, abs_zero]
    linarith
  exact (fourContacts_excluded hh x hs hc).not_ge (hmin _ hy)

/-- The same comparison for the original ordered-pair, all-image physical energy.
Here h is the gap measured as a fraction of the period. -/
theorem physical_fourContacts_excluded {α L h : ℝ} (hα : 0 < α) (hL : 0 < L) (hh : 0 < h)
    (X : Fin 6 → ℝ)
    (hs : (8 ≤ α*L^2 ∧ α*L^2 ≤ 9 ∧ h ≤ 7/100) ∨
      (799/100 ≤ α*L^2 ∧ α*L^2 ≤ 801/100 ∧ h ≤ 1/10))
    (hx : FourContacts h (fun i => X i/L)) :
    physicalEnergy α L (fun i => L*sites h 0 i) < physicalEnergy α L X := by
  rw [physicalEnergy_eq_imageEnergy (N:=6) (by decide) α L hα hL,
    physicalEnergy_eq_imageEnergy (N:=6) (by decide) α L hα hL]
  simpa [hL.ne'] using fourContacts_excluded hh (fun i => X i/L) hs hx

#print axioms fourContacts_excluded
#print axioms physical_fourContacts_excluded

end GaussianChains.Strip
