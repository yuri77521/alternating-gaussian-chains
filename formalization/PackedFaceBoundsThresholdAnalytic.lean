import PackedFaceBoundsImplicit
import PackedFaceModesAnalytic
import PackedFaceSlopesTransition
import Mathlib.Analysis.Analytic.Within

/-! Analyticity of the actual two threshold functions on the paper's nome range. -/
noncomputable section
namespace GaussianChains.PackedFace

open Filter Set Real
open scoped Topology

private def complexEndpointZ (outer : Bool) (x : ℂ) : ℂ :=
  if outer then 3*x-4*x^3 else 1

private theorem complexEndpointZ_ofReal (outer : Bool) (x : ℝ) :
    complexEndpointZ outer (x : ℂ) = (endpointZ outer x : ℂ) := by
  cases outer <;> simp [complexEndpointZ, endpointZ]

private theorem slope_regular_at_floor (outer : Bool) {q : ℝ}
    (hq : q ∈ Ioc 0 faceQ) (h : ℝ) :
    ContDiffAt ℂ 1 (complexFloorSlope (complexEndpointZ outer)) ((q : ℂ), (h : ℂ)) := by
  obtain ⟨hc,hb⟩ := both_complexFloorSlopes_contDiffAt hq.1.le hq.2 h
  cases outer
  · exact hc
  · exact hb

/-- Joint real regularity of the endpoint equation in nome and floor.
In particular mixed variations can use the same derivative as either partial slice. -/
theorem floorSlope_contDiffAt (outer : Bool) {q : ℝ} (hq : q ∈ Ioc 0 faceQ) (h : ℝ) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => floorSlope outer p.1 p.2) (q,h) := by
  let C : ℝ × ℝ → ℂ × ℂ := fun p => ((p.1 : ℂ), (p.2 : ℂ))
  have hC : ContDiffAt ℝ 1 C (q,h) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_fst).prodMk
      (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_snd)
  have hcomp := Complex.reCLM.contDiff.contDiffAt.comp (q,h)
    (((slope_regular_at_floor outer hq h).restrict_scalars ℝ).comp (q,h) hC)
  simpa [Function.comp_def, C, complexFloorSlope_ofReal (complexEndpointZ_ofReal outer), floorSlope]
    using hcomp

/-- Each critical floor has an analytic germ at every admissible nome. At
the right endpoint the germ agrees with the chosen threshold on its physical
domain, regardless of its definition beyond the proved parameter range. -/
theorem criticalFloor_analyticOn (outer : Bool) :
    AnalyticOn ℝ (criticalFloor outer) (Ioc 0 faceQ) := by
  intro q hq
  have hr := criticalFloor_spec outer hq.1 hq.2
  apply analyticWithinAt_simple_real_root
    (F := complexFloorSlope (complexEndpointZ outer))
    (P := fun p : ℝ × ℝ => floorSlope outer p.1 p.2)
    (interval := Ioo (1/8) (1/6)) hq (Ioo_mem_nhds hr.1.1 hr.1.2)
    (slope_regular_at_floor outer hq _)
    (fun t u => complexFloorSlope_ofReal (complexEndpointZ_ofReal outer) t u)
    ((differentiableAt_of_deriv_ne_zero hr.2.2.1).hasDerivAt) hr.2.2.1
  · intro t ht
    exact (criticalFloor_spec outer ht.1 ht.2).2.1
  · intro t ht u hu he
    exact ((criticalFloor_spec outer ht.1 ht.2).2.2.2 u (Ioo_subset_Icc_self hu)).mp he

theorem criticalFloor_analyticAt (outer : Bool) {q : ℝ} (hq : q ∈ Ioo 0 faceQ) :
    AnalyticAt ℝ (criticalFloor outer) q :=
  (criticalFloor_analyticOn outer).analyticAt (Ioc_mem_nhds hq.1 hq.2)

private theorem analyticAt_nome {s : ℝ} (hs : 0 < s) :
    AnalyticAt ℝ (fun t : ℝ => exp (-(π^2)/t)) s := by
  exact (analyticAt_const.div (analyticAt_id (𝕜 := ℝ)) hs.ne').rexp'

theorem criticalFloor_width_analyticOn (outer : Bool) :
    AnalyticOn ℝ (fun s : ℝ => criticalFloor outer (exp (-(π^2)/s)))
      {s : ℝ | 0 < s ∧ exp (-(π^2)/s) ≤ faceQ} := by
  intro s hs
  exact (criticalFloor_analyticOn outer _ ⟨exp_pos _, hs.2⟩).comp
    (f := fun t : ℝ => exp (-(π^2)/t))
    (analyticAt_nome hs.1).analyticWithinAt (fun t ht => ⟨exp_pos _, ht.2⟩)

theorem criticalFloor_width_analyticAt (outer : Bool) {s : ℝ}
    (hs : 0 < s) (hQ : exp (-(π^2)/s) < faceQ) :
    AnalyticAt ℝ (fun t : ℝ => criticalFloor outer (exp (-(π^2)/t))) s :=
  (criticalFloor_analyticAt outer ⟨exp_pos _, hQ⟩).comp
    (f := fun t : ℝ => exp (-(π^2)/t)) (analyticAt_nome hs)

/-- At the included upper endpoint both critical floors agree from the left
with a function analytic on an open neighborhood of that endpoint. -/
theorem criticalFloor_extension_at_upper (outer : Bool) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r faceQ ∧
      EqOn (criticalFloor outer) r (Ioc 0 faceQ) := by
  have hm : faceQ ∈ Ioc 0 faceQ := ⟨by norm_num [faceQ], le_rfl⟩
  obtain ⟨r, _, he, ha⟩ := (criticalFloor_analyticOn outer faceQ hm).exists_analyticAt
  exact ⟨r, ha, he.mono (subset_insert _ _)⟩

end GaussianChains.PackedFace

