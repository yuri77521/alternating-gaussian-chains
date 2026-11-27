import PackedFaceEnergyTable
import PackedFaceBoundsThresholdAnalytic
import PackedFaceReflection

/-! Theorem 3 in the published numbering. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

/-- The small-floor derivative estimate rules out additional roots below the
transition window, including at its left endpoint. -/
theorem unique_root_on_face (outer : Bool) {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (hh : h ∈ Ioc 0 (1/6)) : floorSlope outer q h = 0 ↔ h = criticalFloor outer q := by
  have hr := criticalFloor_spec outer hq hQ
  by_cases h8 : 1/8 ≤ h
  · exact hr.2.2.2 h ⟨h8,hh.2⟩
  have hs : h < 1/8 := lt_of_not_ge h8
  have hp {y : ℝ} (hy : y ∈ Icc 0 2) := phiD_pos_small_floor hq.le hQ hh.1.le hs.le hy
  have he : 0 < floorSlope outer q h := by
    cases outer
    · simpa [phiD_eq_endpointSlope,floorSlope,endpointZ]
        using hp (show (0:ℝ) ∈ Icc 0 2 by constructor <;> norm_num)
    · have hy : coord (bound h) ∈ Icc 0 2 := by
        unfold coord
        constructor <;> linarith [Real.neg_one_le_cos (2*Real.pi*bound h),Real.cos_le_one (2*Real.pi*bound h)]
      simpa [phiD_eq_endpointSlope,outer_abscissa,floorSlope,endpointZ] using hp hy
  exact iff_of_false he.ne' (hs.trans hr.1.1).ne

/-- All global minima **on the closed packed-triple face**. The floor
derivative is nonzero at either endpoint-slope root. Each critical floor
depends analytically and strictly decreasingly on the positive width. -/
theorem theorem_three (s : ℝ) (hs : 0 < s) (hQ : Real.exp (-(Real.pi^2)/s) ≤ 17/50) :
    let q := Real.exp (-(Real.pi^2)/s)
    (∀ outer : Bool,
      let r := criticalFloor outer q
      r ∈ Ioo (1/8) (1/6) ∧ floorSlope outer q r = 0 ∧ deriv (floorSlope outer q) r ≠ 0 ∧
        (∀ h ∈ Ioc 0 (1/6), floorSlope outer q h = 0 ↔ h = r)) ∧
    (∀ outer : Bool,
      let r := fun w : ℝ => criticalFloor outer (Real.exp (-(Real.pi^2)/w))
      let widths := {w : ℝ | 0 < w ∧ Real.exp (-(Real.pi^2)/w) ≤ 17/50}
      AnalyticOn ℝ r widths ∧ StrictAntiOn r widths) ∧
    (∀ h : ℝ, 0 < h → h ≤ 1/6 → PhaseRows s h) := by
  refine ⟨?_,
    fun outer => ⟨criticalFloor_width_analyticOn outer, criticalFloor_width_strictAntiOn outer⟩,
    fun _ h0 h6 => closed_face_energy_table hs hQ h0 h6⟩
  intro outer
  have H := criticalFloor_spec outer (Real.exp_pos _) hQ
  exact ⟨H.1,H.2.1,H.2.2.1,fun _ hh => unique_root_on_face outer (Real.exp_pos _) hQ hh⟩

/-- Each nome in the entire stated interval is the physical nome of exactly one positive width. -/
theorem width_for_nome {q : ℝ} (hq : 0 < q) (hQ : q ≤ 17/50) :
    ∃! s : ℝ, 0 < s ∧ Real.exp (-(Real.pi^2)/s) = q := by
  have hl := Real.log_neg hq (lt_of_le_of_lt hQ (by norm_num))
  have hp : Real.pi^2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  let s := -(Real.pi^2) / Real.log q
  have hs : 0 < s := div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) hl
  have he : Real.exp (-(Real.pi^2)/s) = q := by
    have hlog : -(Real.pi^2)/s = Real.log q := by
      unfold s
      field_simp [hp,hl.ne] <;> ring
    rw [hlog, Real.exp_log hq]
  exact ⟨s,⟨hs, he⟩,fun t ht => nome_strictMonoOn.injOn ht.1 hs (ht.2.trans he.symm)⟩

theorem closed_face_all_nomes {q : ℝ} (hq : 0 < q) (hQ : q ≤ 17/50) :
    ∃ s : ℝ, 0 < s ∧ Real.exp (-(Real.pi^2)/s) = q ∧
      ∀ h : ℝ, 0 < h → h ≤ 1/6 → PhaseRows s h := by
  obtain ⟨s,⟨hs,he⟩,_⟩ := width_for_nome hq hQ
  exact ⟨s,hs,he,fun _ h0 h6 => closed_face_energy_table hs (by simpa only [he] using hQ) h0 h6⟩

#print axioms theorem_three

end GaussianChains.PackedFace




