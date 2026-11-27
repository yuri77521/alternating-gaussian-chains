import PackedFaceGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! One-dimensional closed-interval minimization, retaining weak endpoint slope tests. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

def Minimizes (F : ℝ → ℝ) (S : Set ℝ) (y : ℝ) : Prop :=
  y ∈ S ∧ ∀ v ∈ S, F y ≤ F v

/-- The unique minimum at a sign-changing slope also covers a zero endpoint slope. -/
theorem unique_min_of_slopes {u r : ℝ} {F D : ℝ → ℝ}
    (hr : r ∈ Icc 0 u) (hc : ContinuousOn F (Icc 0 u))
    (hder : ∀ y ∈ Ioo 0 u, HasDerivAt F (D y) y)
    (hl : ∀ y ∈ Ioo 0 r, D y < 0) (hu : ∀ y ∈ Ioo r u, 0 < D y) :
    ∀ y, Minimizes F (Icc 0 u) y ↔ y = r := by
  have left := strictAntiOn_of_deriv_neg (convex_Icc 0 r)
    (hc.mono (Icc_subset_Icc_right hr.2)) (fun x hx => by
      rw [interior_Icc] at hx
      exact (hder x ⟨hx.1, hx.2.trans_le hr.2⟩).deriv.symm ▸ hl x hx)
  have right := strictMonoOn_of_deriv_pos (convex_Icc r u)
    (hc.mono (Icc_subset_Icc_left hr.1)) (fun x hx => by
      rw [interior_Icc] at hx
      exact (hder x ⟨hr.1.trans_lt hx.1, hx.2⟩).deriv.symm ▸ hu x hx)
  have hlt (x : ℝ) (hx : x ∈ Icc 0 u) (hne : x ≠ r) : F r < F x := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact left ⟨hx.1, h.le⟩ ⟨hr.1, le_rfl⟩ h
    · exact right ⟨le_rfl, hr.2⟩ ⟨h.le, hx.2⟩ h
  intro y
  constructor
  · intro hy
    by_contra hn
    exact (hlt y hy.1 hn).not_ge (hy.2 r hr)
  · rintro rfl
    refine ⟨hr, fun v hv => ?_⟩
    rcases eq_or_ne v y with rfl | hn
    · exact le_rfl
    · exact (hlt v hv hn).le

theorem min_at_zero_of_leftSlope_nonneg {u : ℝ} {F D : ℝ → ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn F (Icc 0 u)) (hd : ∀ y ∈ Ioo 0 u, HasDerivAt F (D y) y)
    (hm : StrictMonoOn D (Icc 0 u)) (hz : 0 ≤ D 0) :
    ∀ y, Minimizes F (Icc 0 u) y ↔ y = 0 := by
  apply unique_min_of_slopes ⟨le_rfl,hu⟩ hc hd
  · intro y hy
    exact (hy.2.not_ge hy.1.le).elim
  · intro y hy
    exact hz.trans_lt (hm ⟨le_rfl,hu⟩ ⟨hy.1.le,hy.2.le⟩ hy.1)

theorem min_at_end_of_rightSlope_nonpos {u : ℝ} {F D : ℝ → ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn F (Icc 0 u)) (hd : ∀ y ∈ Ioo 0 u, HasDerivAt F (D y) y)
    (hm : StrictMonoOn D (Icc 0 u)) (hz : D u ≤ 0) :
    ∀ y, Minimizes F (Icc 0 u) y ↔ y = u := by
  apply unique_min_of_slopes ⟨hu,le_rfl⟩ hc hd
  · intro y hy
    exact (hm ⟨hy.1.le,hy.2.le⟩ ⟨hu,le_rfl⟩ hy.2).trans_le hz
  · intro y hy
    exact (hy.2.not_ge hy.1.le).elim

theorem min_at_unique_interior_root {u : ℝ} {F D : ℝ → ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn F (Icc 0 u)) (hd : ∀ y ∈ Ioo 0 u, HasDerivAt F (D y) y)
    (hm : StrictMonoOn D (Icc 0 u)) (hD : ContinuousOn D (Icc 0 u))
    (hl : D 0 < 0) (hr : 0 < D u) :
    ∃ r ∈ Ioo 0 u, D r = 0 ∧
      (∀ z ∈ Icc 0 u, D z = 0 ↔ z = r) ∧
      (∀ y, Minimizes F (Icc 0 u) y ↔ y = r) := by
  obtain ⟨r, hru, hDr⟩ := intermediate_value_Icc hu hD (show (0:ℝ) ∈ Icc (D 0) (D u) from ⟨hl.le,hr.le⟩)
  have hrpos : 0 < r := lt_of_le_of_ne hru.1 (fun h => by rw [← h] at hDr; exact hl.ne hDr)
  have hrlt : r < u := lt_of_le_of_ne hru.2 (fun h => by rw [h] at hDr; exact hr.ne' hDr)
  refine ⟨r,⟨hrpos,hrlt⟩,hDr,?_,?_⟩
  · intro z hz
    rw [← hDr]
    exact ⟨hm.injOn hz hru, congrArg D⟩
  · apply unique_min_of_slopes hru hc hd
    · intro z hz
      simpa only [hDr] using hm ⟨hz.1.le, hz.2.le.trans hru.2⟩ hru hz.2
    · intro z hz
      simpa only [hDr] using hm hru ⟨hru.1.trans hz.1.le, hz.2.le⟩ hz.1

/-- Every squared coordinate has both reflected preimages, with one preimage at the origin. -/
theorem minimizes_comp_coord_iff (F : ℝ → ℝ) {h t : ℝ} (hh : 0 ≤ h) (h6 : h ≤ 1/6)
    (ht : feasible h t) :
    Minimizes (fun u => F (coord u)) {u | feasible h u} t ↔
      Minimizes F (Icc 0 (coord (bound h))) (coord t) := by
  have mem (v : ℝ) (hv : feasible h v) : coord v ∈ Icc 0 (coord (bound h)) := by
    rw [← coord_image h hh h6]
    exact ⟨|v|,⟨abs_nonneg _,hv⟩,coord_abs _⟩
  refine ⟨fun H => ⟨mem t ht, ?_⟩, fun H => ⟨ht, fun v hv => H.2 _ (mem v hv)⟩⟩
  intro z hz
  rw [← coord_image h hh h6] at hz
  rcases hz with ⟨v,hv,rfl⟩
  exact H.2 v (show feasible h v by simpa [feasible,abs_of_nonneg hv.1] using hv.2)

end GaussianChains.PackedFace
