import BifurcationJets
import BifurcationCertificate
import BifurcationClassification
import PackedFaceCurvatureSigns
import Mathlib.Analysis.Real.Pi.Bounds

/-! Width-eight critical floor, physical derivative enclosures and pitch coefficients. -/
noncomputable section
namespace GaussianChains.Bifurcation

open Images PackedFace Set

def qEight := Real.exp (-(Real.pi^2)/8)
def hcEight := criticalFloor false qEight
def faceEnergy (h t : ℝ) := imageEnergy 8 (sites h t)
theorem faceEnergy_eq_physicalEnergy (h t : ℝ) :
    faceEnergy h t = physicalEnergy 8 1 (sites h t) := by
  simpa [faceEnergy] using (physicalEnergy_eq_imageEnergy (N := 6) (by norm_num)
    8 1 (by norm_num) (by norm_num) (sites h t)).symm

def kappa (h : ℝ) := deriv (deriv (faceEnergy h)) 0
def mixedCritical := deriv kappa hcEight
def fourthCritical := iteratedDeriv 4 (faceEnergy hcEight) 0

theorem qEight_le : qEight ≤ faceQ := nome_eight_le_faceQ

theorem critical_zero : iteratedDeriv 2 (faceEnergy hcEight) 0 = 0 := by
  have H := (criticalFloor_spec false (Real.exp_pos _) qEight_le).1
  have hh : 0 < hcEight := lt_trans (by norm_num : (0:ℝ)<1/8) H.1
  have Z := (centered_curvature_signs (by norm_num : (0:ℝ)<8) qEight_le hh H.2.le).2.1 rfl
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,faceEnergy] using Z

theorem root_floor_bounds : (lowerFloor:ℝ) < hcEight ∧ hcEight < (upperFloor:ℝ) := by
  have hg (h : ℝ) (H : h ∈ Ioo (0:ℝ) (1/6)) :
      (h<hcEight → 0 < curvatureAt .second h) ∧
      (h=hcEight → curvatureAt .second h = 0) ∧
      (hcEight<h → curvatureAt .second h < 0) := by
    have HS := centered_curvature_signs (by norm_num : (0:ℝ)<8) qEight_le H.1 H.2.le
    simpa only [hcEight,qEight,(physical_centered_jets H).1] using HS
  have L := hg (lowerFloor:ℝ) (by constructor <;> norm_num [lowerFloor])
  have U := hg (upperFloor:ℝ) (by constructor <;> norm_num [upperFloor])
  obtain ⟨hp,hn⟩ := root_endpoint_signs
  constructor
  · rcases lt_trichotomy (lowerFloor:ℝ) hcEight with h|h|h
    · exact h
    · linarith [L.2.1 h]
    · linarith [L.2.2 h]
  · rcases lt_trichotomy (upperFloor:ℝ) hcEight with h|h|h
    · linarith [U.1 h]
    · linarith [U.2.1 h]
    · exact h

/-- Every number here refers to a derivative of the physical energy at the
unique centered face threshold of the frozen paper. -/
theorem critical_coefficients :
    (-58.94248 < mixedCritical ∧ mixedCritical < -58.94246) ∧
    (70.22242 < fourthCritical ∧ fourthCritical < 70.22244) ∧
    (0.40191212 < deriv (fun h => faceEnergy h 0) hcEight / 4 ∧
      deriv (fun h => faceEnergy h 0) hcEight / 4 < 0.40191214) := by
  obtain ⟨hl,hu⟩ := root_floor_bounds
  have hband : rootBand.Mem hcEight := ⟨hl.le, hu.le⟩
  have hh : hcEight ∈ Ioo (0:ℝ) (1/6) := by
    norm_num [lowerFloor] at hl
    norm_num [upperFloor] at hu
    exact ⟨by linarith,by linarith⟩
  unfold mixedCritical fourthCritical kappa faceEnergy
  rw [mixedAt_physical hh,(physical_centered_jets hh).2,inwardAt_physical hh]
  exact coefficients_on_rootBand hband

theorem pitch_coefficients :
    (2.24414 < Real.sqrt (-6*mixedCritical/fourthCritical) ∧
      Real.sqrt (-6*mixedCritical/fourthCritical) < 2.24416) ∧
    (74.2115 < 3*mixedCritical^2/(2*fourthCritical) ∧
      3*mixedCritical^2/(2*fourthCritical) < 74.2119) :=
  coefficient_intervals critical_coefficients.1.1 critical_coefficients.1.2
    critical_coefficients.2.1.1 critical_coefficients.2.1.2

end GaussianChains.Bifurcation
