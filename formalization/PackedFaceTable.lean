import PackedFacePhases
import PackedFaceSlopesTransition

/-! The thresholds and all closed-face displacements in Table 1. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

private theorem center_link (q h : ℝ) : floorSlope false q h = centralSlope q h := by
  simp [centralSlope,phiD_eq_endpointSlope,floorSlope,endpointZ]

private theorem contact_link (q h : ℝ) : floorSlope true q h = contactSlope q h := by
  simp [contactSlope,phiD_eq_endpointSlope,floorSlope,endpointZ,outer_abscissa]

private theorem floor_strictAnti (outer : Bool) {q : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ) :
    StrictAntiOn (floorSlope outer q) (Icc (1/8) (1/6)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_floorSlope outer hq.le hQ)
  rw [interior_Icc]
  exact fun _ hx => floorSlope_deriv_neg outer hq hQ hx

theorem criticalFloor_order {q : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ) :
    criticalFloor false q < criticalFloor true q := by
  let c := criticalFloor false q
  have hc := criticalFloor_spec false hq hQ
  have hb := criticalFloor_spec true hq hQ
  apply ordered_endpoint_roots (Ioo_subset_Icc_self hc.1) (Ioo_subset_Icc_self hb.1)
    (floor_strictAnti true hq hQ) _ hb.2.1
  rw [contact_link]
  have hz := hc.2.1
  rw [center_link] at hz
  change phiD q (criticalFloor false q) 0 = 0 at hz
  have hct : 0 < coord (bound c) := by
    have hm := strictMonoOn_coord
    have hbp : 0 < bound c := by unfold bound c; linarith [hc.1.2]
    have hbu : bound c ≤ 1/2 := by unfold bound c; linarith [hc.1.1]
    simpa using hm (by constructor <;> norm_num) ⟨hbp.le,hbu⟩ hbp
  have hy : coord (bound c) ≤ 2 := by unfold coord; linarith [Real.neg_one_le_cos (2*Real.pi*bound c)]
  exact hz ▸ strictMonoOn_phiD_large hq hQ hc.1.1.le hc.1.2.le
    (by constructor <;> norm_num) ⟨hct.le,hy⟩ hct

/-- Score version of the entire phase table; comparison with physical energy is Eq. (9). -/
theorem closed_face_score_table {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h0 : 0 < h) (h6 : h ≤ 1/6) :
    (h ≤ criticalFloor false q →
      ∀ t, Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔ t = 0) ∧
    (criticalFloor false q < h → h < criticalFloor true q →
      ∃ t₀ ∈ Ioo 0 (bound h), phiD q h (coord t₀) = 0 ∧
        ∀ t, Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔ t = t₀ ∨ t = -t₀) ∧
    (criticalFloor true q ≤ h → h < 1/6 →
      ∀ t, Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔
        t = bound h ∨ t = -(bound h)) ∧
    (h = 1/6 → ∀ t, Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔ t = 0) := by
  have hc := criticalFloor_spec false hq hQ
  have hb := criticalFloor_spec true hq hQ
  have mc := floor_strictAnti false hq hQ
  have mb := floor_strictAnti true hq hQ
  refine ⟨?_,?_,?_,?_⟩
  · intro hh t
    rcases le_total h (1/8) with h8 | h8
    · exact small_floor_min_iff hq.le hQ h0.le h8 t
    · apply centered_min_iff hq hQ h8 h6 _ t
      have hs := mc.antitoneOn (show h ∈ Icc (1/8) (1/6) from ⟨h8,h6⟩) (Ioo_subset_Icc_self hc.1) hh
      simpa only [hc.2.1,center_link] using hs
  · intro hch hhb
    have h8 := hc.1.1.trans hch
    have hm : h ∈ Icc (1/8) (1/6) := ⟨h8.le,h6⟩
    have hl := mc (Ioo_subset_Icc_self hc.1) hm hch
    have hr := mb hm (Ioo_subset_Icc_self hb.1) hhb
    rw [hc.2.1,center_link] at hl
    rw [hb.2.1,contact_link] at hr
    obtain ⟨v,hv,hz,_,H⟩ := interior_min_pair hq hQ h8.le h6 hl hr
    exact ⟨v,hv,hz,H⟩
  · intro hbh _ t
    have h8 := hb.1.1.le.trans hbh
    apply contact_min_iff hq hQ h8 h6 _ t
    have hs := mb.antitoneOn (Ioo_subset_Icc_self hb.1) (show h ∈ Icc (1/8) (1/6) from ⟨h8,h6⟩) hbh
    simpa only [hb.2.1,contact_link] using hs
  · rintro rfl t
    exact uniform_min_iff _ t

end GaussianChains.PackedFace
