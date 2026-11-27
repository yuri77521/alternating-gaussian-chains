import PhaseStripFinite
import PhaseStripTails
import PhaseStripRootsInputs
import PackedFaceSlopesTransition
import ClustersWidth

/-! An interval bound for the actual infinite endpoint derivative and an
open bracket test for the two uniquely defined critical floors. -/
namespace GaussianChains.PhaseStrip

open GaussianChains.Cert GaussianChains.PackedFace Set

def encloses (A B : Interval) : Prop := A.lo ≤ B.lo ∧ B.hi ≤ A.hi

instance (A B : Interval) : Decidable (encloses A B) := by unfold encloses; infer_instance

theorem encloses_mem {A B : Interval} (h : encloses A B) {v : ℝ} (hv : B.Mem v) : A.Mem v :=
  ⟨(Rat.cast_le.mpr h.1).trans hv.1, hv.2.trans (Rat.cast_le.mpr h.2)⟩

/-- Six retained modes and the symmetric bound on every omitted mode. -/
def slopeBox (outer : Bool) (Q X : Interval) : Interval :=
  (sixBox .value outer Q X).add ⟨-2/10^20,2/10^20⟩

theorem slopeBox_mem (outer : Bool) {q x : ℝ} {Q X : Interval}
    (hq : 0 ≤ q) (hq' : q ≤ faceQ) (hx : x ∈ Icc (-1) 1)
    (hz : endpointZ outer x ∈ Icc (-1) 1) (hQ : Q.Mem q) (hX : X.Mem x) :
    (slopeBox outer Q X).Mem (endpointSlope q x (endpointZ outer x)) := by
  let v := ∑ k ∈ Finset.range 6, endpointMode (k+1) q x (endpointZ outer x)
  have hfinite : (sixBox .value outer Q X).Mem v := sixBox_mem .value outer hQ hX
  have herr := abs_le.mp (slope_six_error hq hq' hx hz).le
  have ht : (⟨-2/10^20,2/10^20⟩ : Interval).Mem
      (endpointSlope q x (endpointZ outer x)-v) := by
    exact ⟨le_trans (by norm_num : ((-2/10^20:ℚ):ℝ) ≤ -(2/10^20:ℝ)) herr.1,
      le_trans herr.2 (by norm_num : (2/10^20:ℝ) ≤ ((2/10^20:ℚ):ℝ))⟩
  have hv : v+(endpointSlope q x (endpointZ outer x)-v) =
      endpointSlope q x (endpointZ outer x) := by ring
  exact hv ▸ Interval.add_mem hfinite ht

/-- In the transition band both real Chebyshev arguments belong to [-1,1].
The outer argument is a cosine of a genuine displacement angle. -/
theorem floor_endpoint_range (outer : Bool) (h : ℝ) :
    endpointZ outer (Real.cos (2*Real.pi*h)) ∈ Icc (-1) 1 := by
  cases outer
  · norm_num [endpointZ]
  · change 3*Real.cos (2*Real.pi*h)-4*Real.cos (2*Real.pi*h)^3 ∈ _
    rw [← outer_abscissa]
    unfold coord
    simpa using And.intro (Real.neg_one_le_cos (2*Real.pi*bound h))
      (Real.cos_le_one (2*Real.pi*bound h))

/-- A box may contain a larger rational input enclosure certified elsewhere. -/
theorem floorSlope_mem (outer : Bool) {q h : ℝ} {Q X : Interval}
    (hq : 0 ≤ q) (hq' : q ≤ faceQ) (hQ : Q.Mem q)
    (hX : X.Mem (Real.cos (2*Real.pi*h))) : (slopeBox outer Q X).Mem (floorSlope outer q h) :=
  slopeBox_mem outer hq hq' ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
    (floor_endpoint_range outer h) hQ hX

/-- In the full closed width strip the physical nome obeys the face hypothesis. -/
theorem strip_nome_le_faceQ {s : ℝ} (hlo : 8 ≤ s) (hhi : s ≤ 9) :
    Real.exp (-(Real.pi^2)/s) ≤ faceQ := by
  simpa only [faceQ,neg_div] using (nome_lt_seventeen_fiftieths (by linarith) hhi).le

/-- Accepted strict signs bound the unique root, not merely one zero of a
truncated Fourier series. -/
theorem criticalFloor_bracket (outer : Bool) {q l u : ℝ} (hq : 0 < q)
    (hq' : q ≤ faceQ) (hl : 1/8 ≤ l) (hu : u ≤ 1/6) (hlu : l ≤ u)
    (hpos : 0 < floorSlope outer q l) (hneg : floorSlope outer q u < 0) :
    l < criticalFloor outer q ∧ criticalFloor outer q < u := by
  have hc := (continuousOn_floorSlope outer hq.le hq').mono (Icc_subset_Icc hl hu)
  obtain ⟨r,hr,he⟩ := intermediate_value_Ioo' hlu hc (show (0:ℝ) ∈ Ioo _ _ from ⟨hneg,hpos⟩)
  have hsame := ((criticalFloor_spec outer hq hq').2.2.2 r
    ⟨hl.trans hr.1.le,hr.2.le.trans hu⟩).mp he
  simpa only [← hsame] using hr

/-- Reusable rational input check for the 17-decimal table and for the
coarser root boxes used to localize a whole parameter slab. -/
theorem criticalFloor_in_bracket (outer : Bool) {s l u : ℚ} {Q Xl Xu : Interval}
    (hs : 8 ≤ s) (hs' : s ≤ 9) (hl : 1/8 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1/6)
    (hQ : encloses Q (qInput s)) (hXl : encloses Xl (xInput l)) (hXu : encloses Xu (xInput u))
    (hplus : 0 < (slopeBox outer Q Xl).lo) (hminus : (slopeBox outer Q Xu).hi < 0) :
    (l:ℝ) < criticalFloor outer (Real.exp (-(Real.pi^2)/(s:ℝ))) ∧
      criticalFloor outer (Real.exp (-(Real.pi^2)/(s:ℝ))) < (u:ℝ) := by
  let q := Real.exp (-(Real.pi^2)/(s:ℝ))
  have hpos : 0 < q := Real.exp_pos _
  have hcap : q ≤ faceQ := strip_nome_le_faceQ (by exact_mod_cast hs) (by exact_mod_cast hs')
  have hq : Q.Mem q := encloses_mem hQ (qInput_mem hs hs')
  have hlo := floorSlope_mem outer hpos.le hcap hq (encloses_mem hXl (xInput_mem hl (hlu.trans hu)))
  have hhi := floorSlope_mem outer hpos.le hcap hq (encloses_mem hXu (xInput_mem (hl.trans hlu) hu))
  have hlR : 1/8 ≤ (l:ℝ) := by simpa using (Rat.cast_le.mpr hl : ((1/8:ℚ):ℝ) ≤ (l:ℝ))
  have huR : (u:ℝ) ≤ 1/6 := by simpa using (Rat.cast_le.mpr hu : (u:ℝ) ≤ ((1/6:ℚ):ℝ))
  exact criticalFloor_bracket outer hpos hcap hlR huR
    (by exact_mod_cast hlu) ((by exact_mod_cast hplus : (0:ℝ) < ((slopeBox outer Q Xl).lo:ℝ)).trans_le hlo.1)
    (hhi.2.trans_lt (by exact_mod_cast hminus))

end GaussianChains.PhaseStrip
