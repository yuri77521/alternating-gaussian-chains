import PackedFaceBoundsThresholdDerivative
import ClustersWidth

/-! The physical-width derivatives of the two actual implicit roots in
Theorem 5. The common factor is kept outside the difference of their two
fractions, as required by the correlated interval estimate. -/
noncomputable section
namespace GaussianChains.PhaseStrip

open Real Set PackedFace

def widthNome (s : ℝ) : ℝ := exp (-(π^2)/s)
def thresholdX (outer : Bool) (q : ℝ) : ℝ := cos (2*π*criticalFloor outer q)
def phaseWidth (s : ℝ) : ℝ :=
  criticalFloor true (widthNome s) - criticalFloor false (widthNome s)

def phaseFactor (outer : Bool) (q x : ℝ) : ℝ :=
  (q * ∑' k : ℕ, endpointDq (k+1) q x (endpointZ outer x)) /
    (sqrt (1-x^2) * ∑' k : ℕ, endpointDx (k+1) q x (endpointZ outer x) (endpointZ' outer x))

theorem criticalFloor_s_hasDerivAt (outer : Bool) {s : ℝ} (hs : 0<s)
    (hQ : widthNome s < faceQ) :
    HasDerivAt (fun u => criticalFloor outer (widthNome u))
      ((π/(2*s^2)) * phaseFactor outer (widthNome s) (thresholdX outer (widthNome s))) s := by
  let q := widthNome s
  let h := criticalFloor outer q
  let x := thresholdX outer q
  have hq : 0<q := Real.exp_pos _
  have hslope := criticalFloor_spec outer hq hQ.le
  have hh : h ∈ Ioo (1/8) (1/6) := hslope.1
  have hx : x ∈ Ioo (1/2) (√2/2) := cos_floor_mem_open hh
  have hpath := endpointSlope_hasDerivAt_x hq.le hQ.le hx
    (fun v hv => z_range outer (Ioo_subset_Icc_self hv))
    (fun v hv => z_path outer (Ioo_subset_Icc_self hv))
  let D := ∑' k : ℕ, endpointDx (k+1) q x (endpointZ outer x) (endpointZ' outer x)
  let P := ∑' k : ℕ, endpointDq (k+1) q x (endpointZ outer x)
  have htpos : 0 < 2*π*h := by
    have : 0<h := lt_trans (by norm_num) hh.1
    positivity
  have htlt : 2*π*h < π := by
    nlinarith [mul_pos pi_pos (sub_pos.mpr hh.2), pi_pos]
  have hsin : sin (2*π*h) = sqrt (1-x^2) :=
    sin_eq_sqrt_one_sub_cos_sq htpos.le htlt.le
  have hsin' : sqrt (1-x^2) ≠ 0 := hsin ▸ (sin_pos_of_pos_of_lt_pi htpos htlt).ne'
  have hden : deriv (floorSlope outer q) h = D * (-(sqrt (1-x^2)) * (2*π)) := by
    rw [floorSlope_deriv_eq outer hq.le hQ.le hh, hsin]
    change deriv (fun v => endpointSlope q v (endpointZ outer v)) x * _ = _
    rw [hpath.deriv]
  have hD : D ≠ 0 := by
    intro hD₀
    exact hslope.2.2.1 (by rw [show criticalFloor outer q=h from rfl, hden, hD₀, zero_mul])
  have had := (criticalFloor_hasDerivAt outer hq hQ).comp s (nome_hasDerivAt hs)
  change HasDerivAt _ ((-P / deriv (floorSlope outer q) h) * (π^2*q/s^2)) s at had
  change HasDerivAt _ ((π/(2*s^2)) * ((q*P)/(sqrt (1-x^2)*D))) s
  convert had using 1
  rw [hden]
  field_simp [hD,hsin',pi_ne_zero,hs.ne']

/-- Strictly inside the nome range throughout the closed physical width strip,
so these are two-sided derivatives even at both strip endpoints. -/
theorem phaseWidth_hasDerivAt {s : ℝ} (h8 : 8≤s) (h9 : s≤9) :
    HasDerivAt phaseWidth
      ((π/(2*s^2)) * (phaseFactor true (widthNome s) (thresholdX true (widthNome s)) -
        phaseFactor false (widthNome s) (thresholdX false (widthNome s)))) s := by
  have hs : 0 < s := by linarith
  have hQ : widthNome s < faceQ := by
    simpa [widthNome, faceQ, neg_div] using nome_lt_seventeen_fiftieths hs h9
  simpa only [phaseWidth, mul_sub] using
    (criticalFloor_s_hasDerivAt true hs hQ).sub (criticalFloor_s_hasDerivAt false hs hQ)

/-- Transfer a strict lower interval estimate for the physical derivative to
unique attainment of the least and greatest phase width at 8 and 9. -/
theorem phaseWidth_endpoint_extrema_of_positive
    (hp : ∀ s ∈ Ioo (8:ℝ) 9, 0 < (π/(2*s^2)) *
      (phaseFactor true (widthNome s) (thresholdX true (widthNome s)) -
       phaseFactor false (widthNome s) (thresholdX false (widthNome s)))) :
    StrictMonoOn phaseWidth (Icc 8 9) ∧
    ∀ s ∈ Icc (8:ℝ) 9, (phaseWidth 8 ≤ phaseWidth s ∧ phaseWidth s ≤ phaseWidth 9) ∧
      (phaseWidth s = phaseWidth 8 ↔ s=8) ∧ (phaseWidth s = phaseWidth 9 ↔ s=9) := by
  have hm : StrictMonoOn phaseWidth (Icc 8 9) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs
      exact (phaseWidth_hasDerivAt hs.1 hs.2).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(phaseWidth_hasDerivAt hs.1.le hs.2.le).deriv]
      exact hp s hs
  refine ⟨hm, ?_⟩
  intro s hs
  have h8 : (8:ℝ) ∈ Icc 8 9 := by norm_num
  have h9 : (9:ℝ) ∈ Icc 8 9 := by norm_num
  exact ⟨⟨hm.monotoneOn h8 hs hs.1, hm.monotoneOn hs h9 hs.2⟩,
    ⟨fun e => hm.injOn hs h8 e, fun e => congrArg phaseWidth e⟩,
    ⟨fun e => hm.injOn hs h9 e, fun e => congrArg phaseWidth e⟩⟩

#print axioms phaseWidth_hasDerivAt

end GaussianChains.PhaseStrip
