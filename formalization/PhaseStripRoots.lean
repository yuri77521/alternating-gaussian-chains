import PhaseStripRootsData

/-! Table 2 of the frozen article. Both ends of each decimal bracket are
strict and are checked against the infinite slope at the physical nome. -/
namespace GaussianChains.PhaseStrip
open GaussianChains.PackedFace Set

/-- The ten individual critical floors in the fixed table, identified with the
unique simple zero of the corresponding endpoint slope. -/
theorem table2_critical_floors {r : RootRow} (hr : r ∈ rootRows) :
    let q := Real.exp (-(Real.pi^2)/(r.width:ℝ))
    let c := criticalFloor r.outer q
    (r.lower : ℝ) < c ∧ c < (r.upper : ℝ) ∧
      floorSlope r.outer q c = 0 ∧ deriv (floorSlope r.outer q) c ≠ 0 ∧
      ∀ h ∈ Icc (1/8:ℝ) (1/6), floorSlope r.outer q h = 0 ↔ h = c := by
  obtain ⟨hs,hs',hl,hlu,hu,hQ,hXl,hXu,hpos,hneg⟩ := table_checks_spec hr
  obtain ⟨hb₁,hb₂⟩ := criticalFloor_in_bracket r.outer hs hs' hl hlu.le hu hQ hXl hXu hpos hneg
  have hc := criticalFloor_spec r.outer (Real.exp_pos (-(Real.pi^2)/(r.width:ℝ)))
    (strip_nome_le_faceQ (by exact_mod_cast hs) (by exact_mod_cast hs'))
  exact ⟨hb₁,hb₂,hc.2⟩

/-- The same zero is witnessed in the full packed-face derivative. -/
theorem table2_face_slope_zero {r : RootRow} (hr : r ∈ rootRows) :
    let q := Real.exp (-(Real.pi^2)/(r.width:ℝ))
    let c := criticalFloor r.outer q
    phiD q c (if r.outer then coord (bound c) else 0) = 0 := by
  dsimp only
  let q := Real.exp (-(Real.pi^2)/(r.width:ℝ))
  let c := criticalFloor r.outer q
  change phiD q c _ = 0
  have hz : floorSlope r.outer q c = 0 := (table2_critical_floors hr).2.2.1
  rw [phiD_eq_endpointSlope]
  simpa only [floorSlope,endpointZ] using
    (show endpointSlope q (Real.cos (2*Real.pi*c)) (1-(if r.outer then coord (bound c) else 0)) = 0 by
      cases e : r.outer <;> simpa [e,floorSlope,endpointZ,outer_abscissa] using hz)

#print axioms table2_critical_floors
#print axioms table2_face_slope_zero

/-- The two endpoint brackets also separate the curves at every intermediate
width of the slab, because both critical functions decrease in physical width. -/
theorem slab_separation {a b : RootRow} (ha : a ∈ rootRows) (hb : b ∈ rootRows)
    (ha' : a.outer = false) (hb' : b.outer = true) {s : ℝ}
    (hl : (a.width:ℝ) ≤ s) (hu : s ≤ (b.width:ℝ)) :
    (b.lower : ℝ) - (a.upper : ℝ) <
      criticalFloor true (Real.exp (-(Real.pi^2)/s)) -
      criticalFloor false (Real.exp (-(Real.pi^2)/s)) := by
  let q (v : ℝ) := Real.exp (-(Real.pi^2)/v)
  let S := {v : ℝ | 0 < v ∧ q v ≤ faceQ}
  have h₁ := table_checks_spec ha
  have h₂ := table_checks_spec hb
  have inS {v : ℝ} (h : 8 ≤ v) (h' : v ≤ 9) : v ∈ S :=
    ⟨by linarith,strip_nome_le_faceQ h h'⟩
  have haS : (a.width:ℝ) ∈ S := inS (by exact_mod_cast h₁.1) (by exact_mod_cast h₁.2.1)
  have hbS : (b.width:ℝ) ∈ S := inS (by exact_mod_cast h₂.1) (by exact_mod_cast h₂.2.1)
  have hsS : s ∈ S := inS ((by exact_mod_cast h₁.1 : (8:ℝ) ≤ a.width).trans hl)
    (hu.trans (by exact_mod_cast h₂.2.1))
  have hleft := (criticalFloor_width_strictAntiOn false).antitoneOn haS hsS hl
  have hright := (criticalFloor_width_strictAntiOn true).antitoneOn hsS hbS hu
  have huA := (table2_critical_floors ha).2.1
  have hlB := (table2_critical_floors hb).1
  rw [ha'] at huA
  rw [hb'] at hlB
  exact sub_lt_sub (hlB.trans_le hright) (hleft.trans_lt huA)

/-- The four adjacent slabs exhaust the closed interval [8,9]. -/
theorem phase_width_gt_00114 {s : ℝ} (hs : s ∈ Icc 8 9) :
    0.00114 <
      criticalFloor true (Real.exp (-(Real.pi^2)/s)) -
      criticalFloor false (Real.exp (-(Real.pi^2)/s)) := by
  have use_slab {a b : RootRow} (hmA : a ∈ rootRows) (hmB : b ∈ rootRows)
      (hA : a.outer = false) (hB : b.outer = true) (hL : (a.width:ℝ) ≤ s) (hU : s ≤ (b.width:ℝ))
      (hgap : (0.00114:ℚ) < b.lower-a.upper) :=
    (show (0.00114:ℝ) < (b.lower:ℝ)-(a.upper:ℝ) by
      simpa using (Rat.cast_lt.mpr hgap : ((0.00114:ℚ):ℝ) < ((b.lower-a.upper:ℚ):ℝ))).trans
      (slab_separation hmA hmB hA hB hL hU)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := table_adjacent_clearance
  rcases le_total s (33/4:ℝ) with h8 | h8
  · exact use_slab (a:=row8Center) (b:=row825Contact) (by simp [rootRows]) (by simp [rootRows]) rfl rfl
      (by simpa [row8Center] using hs.1) (by simpa [row825Contact] using h8) h₁
  rcases le_total s (17/2:ℝ) with h85 | h85
  · exact use_slab (a:=row825Center) (b:=row85Contact) (by simp [rootRows]) (by simp [rootRows]) rfl rfl
      (by simpa [row825Center] using h8) (by simpa [row85Contact] using h85) h₂
  rcases le_total s (35/4:ℝ) with h875 | h875
  · exact use_slab (a:=row85Center) (b:=row875Contact) (by simp [rootRows]) (by simp [rootRows]) rfl rfl
      (by simpa [row85Center] using h85) (by simpa [row875Contact] using h875) h₃
  · exact use_slab (a:=row875Center) (b:=row9Contact) (by simp [rootRows]) (by simp [rootRows]) rfl rfl
      (by simpa [row875Center] using h875) (by simpa [row9Contact] using hs.2) h₄

#print axioms phase_width_gt_00114

end GaussianChains.PhaseStrip
