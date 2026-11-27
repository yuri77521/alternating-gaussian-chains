import Point22Curvature
import Point22CurvatureNumbers
import Point22Hessian

/-! Exact rational dyadic coverage of the five second-derivative intervals
in the local width-22 proof. Only the two nearest images need evaluation. -/

namespace GaussianChains.Point22.Curvature
open GaussianChains.Cert GaussianChains.CertExp Set

private theorem singleBox_sound {a b : ℚ} {x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) : (singleBox a b).Mem (gaussian₂ x) := by
  have h' : a ≤ b := by exact_mod_cast hx.1.trans hx.2
  have hpos : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  have hxb := hpos.trans hx.1
  have h₁ := pow_le_pow_left₀ hpos hx.1 2
  have h₂ := pow_le_pow_left₀ hxb hx.2 2
  have boxH (u : ℚ) (hu : u ∈ Icc (0:ℚ) 1) := negExpBox_sound
    (x := 22*u^2) (by positivity) (by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])
  have e := (boxH b ⟨ha.trans h',hb⟩).1
  have f := (boxH a ⟨ha,h'.trans hb⟩).2
  push_cast at e f
  unfold gaussian₂ singleBox
  apply Interval.mul_mem
  · unfold Interval.Mem
    push_cast
    constructor <;> linarith
  · constructor
    · exact e.trans (Real.exp_le_exp.mpr (by linarith only [h₂]))
    · exact (Real.exp_le_exp.mpr (by linarith only [h₁])).trans f

theorem rawBox_sound {a b : ℚ} {x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) : (rawBox a b).Mem (kernel₂ x) := by
  have h1 := singleBox_sound ha hb hx
  have h2 := singleBox_sound (a := 1-b) (b := 1-a) (x := 1-x)
    (sub_nonneg.mpr hb) (by linarith) (by push_cast; constructor <;> linarith [hx.1,hx.2])
  have hr := abs_le.mp (kernel₂_two_images (x := x)
    ⟨(show (0:ℝ) ≤ (a:ℝ) by exact_mod_cast ha).trans hx.1,
      hx.2.trans (by exact_mod_cast hb)⟩)
  have hev : gaussian₂ (x-1) = gaussian₂ (1-x) := by
    unfold gaussian₂
    rw [show x-1=-(1-x) by ring, neg_sq]
  rw [hev] at hr
  have ht : (⟨-1/100,1/100⟩ : Interval).Mem (kernel₂ x - (gaussian₂ x+gaussian₂ (1-x))) := by
    change (((-1/100:ℚ):ℝ) ≤ _) ∧ _ ≤ ((1/100:ℚ):ℝ)
    push_cast
    constructor <;> linarith only [hr.1,hr.2]
  simpa [rawBox] using Interval.add_mem (Interval.add_mem h1 h2) ht

noncomputable def packed₂ (x : ℝ) : ℝ := kernel₂ (x-1/1000) - kernel₂ x + kernel₂ (x+1/1000)

private theorem packedBox_sound {a b : ℚ} {x : ℝ} (ha : 1/1000 ≤ a) (hb : b ≤ 999/1000)
    (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) : (packedBox a b).Mem (packed₂ x) := by
  have hl : (rawBox (a-1/1000) (b-1/1000)).Mem (kernel₂ (x-1/1000)) := by
    apply rawBox_sound (by linarith) (by linarith)
    push_cast; constructor <;> linarith [hx.1,hx.2]
  have hr : (rawBox (a+1/1000) (b+1/1000)).Mem (kernel₂ (x+1/1000)) := by
    apply rawBox_sound (by linarith) (by linarith)
    push_cast; constructor <;> linarith [hx.1,hx.2]
  have hc := rawBox_sound (a := a) (b := b) (by linarith) (by linarith) hx
  exact Interval.add_mem (Interval.add_mem hl (Interval.neg_mem hc)) hr

private def claim : Test → ℝ → Prop
  | .near, x => kernel₂ x < -38
  | .sides, x => 14 < kernel₂ x
  | .diagonals, x => kernel₂ x < 7
  | .packedSides, x => 14 < packed₂ x
  | .packedDiagonals, x => packed₂ x < 7

private theorem check_sound {k : Test} {a b : ℚ} (h : check k a b = true)
    {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) : claim k x := by
  cases k <;> simp only [check, decide_eq_true_eq] at h <;> obtain ⟨ha,hb,h⟩ := h
  · exact (rawBox_sound ha hb hx).2.trans_lt (by exact_mod_cast h)
  · exact lt_of_lt_of_le (by exact_mod_cast h) (rawBox_sound ha hb hx).1
  · exact (rawBox_sound ha hb hx).2.trans_lt (by exact_mod_cast h)
  · exact lt_of_lt_of_le (by exact_mod_cast h) (packedBox_sound ha hb hx).1
  · exact (packedBox_sound ha hb hx).2.trans_lt (by exact_mod_cast h)

private theorem cover_sound {k : Test} (n : ℕ) {a b : ℚ} (h : cover k n a b = true)
    {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) : claim k x := by
  induction n generalizing a b with
  | zero => exact check_sound h hx
  | succ n ih =>
    simp only [cover, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hl,hr⟩
    · exact check_sound h hx
    · rcases le_total x (((a+b)/2:ℚ):ℝ) with hL|hR
      · exact ih hl ⟨hx.1,hL⟩
      · exact ih hr ⟨hR,hx.2⟩

theorem kernel₂_near {x : ℝ} (hx : x ∈ Icc (0:ℝ) (4/100)) : kernel₂ x < -38 :=
  cover_sound 0 near_ok (by simpa using hx)

theorem kernel₂_sides {x : ℝ} (hx : x ∈ Icc (21/100:ℝ) (33/100)) : 14 < kernel₂ x :=
  cover_sound 4 sides_ok (by simpa using hx)

theorem kernel₂_diagonals {x : ℝ} (hx : x ∈ Icc (42/100:ℝ) (58/100)) : kernel₂ x < 7 :=
  cover_sound 4 diag_ok (by simpa using hx)

theorem packed₂_sides {x : ℝ} (hx : x ∈ Icc (21/100:ℝ) (31/100)) : 14 < packed₂ x :=
  cover_sound 7 pack_sides_ok (by simpa using hx)

theorem packed₂_diagonals {x : ℝ} (hx : x ∈ Icc (42/100:ℝ) (58/100)) : packed₂ x < 7 :=
  cover_sound 8 pack_diag_ok (by simpa using hx)

theorem packed₂_one_sub (x : ℝ) : packed₂ (1-x) = packed₂ x := by
  unfold packed₂
  rw [show 1-x-1/1000=1-(x+1/1000) by ring, show 1-x+1/1000=1-(x-1/1000) by ring]
  simp only [kernel₂_one_sub]
  ring

/-- The six required signs hold simultaneously at every point of the closed local domain. -/
theorem certifiedBounds {p : Point} (hp : p ∈ localDomain) : KernelBoundsAt kernel₂ packed₂ p := by
  apply kernelBoundsAt_of_intervals hp _ _ _ _ packed₂_one_sub
  · intro x hx
    exact (kernel₂_sides ⟨hx.1, hx.2.trans (by norm_num)⟩).le
  · exact fun x hx => (packed₂_sides hx).le
  · exact fun x hx => (kernel₂_diagonals hx).le
  · exact fun x hx => (packed₂_diagonals hx).le

#print axioms certifiedBounds
#print axioms kernel₂_near

end GaussianChains.Point22.Curvature
