import Point22Capture
import Point22CurvatureCertificate
import CertRootDerivative
import Point22SixScore
import ChainMinimum
import Mathlib.Data.Fin.VecNotation

/-! Certified cost of opening a previously tight triple in the local six-site cell. -/
noncomputable section
namespace GaussianChains.Point22
open Set Curvature Root22

def openedSites (p : Point) (u v : ℝ) : Fin 6 → ℝ :=
  ![-v,u-v,u,p.1,p.2.1,p.2.2]

set_option maxHeartbeats 2000000 in
/-- Full unordered score decomposes into the variable part and the three external pairs. -/
theorem openedSites_score (s : ℝ) (p : Point) (u v : ℝ) :
    pairScore s (openedSites p u v) = shortGapScore (kernel s) p u v
      - kernel s (p.2.1-p.1) + kernel s (p.2.2-p.1) - kernel s (p.2.2-p.2.1) := by
  rw [six_score_terms]
  generalize kernel s = G
  simp only [show openedSites p u v 0 = -v from rfl,
    show openedSites p u v 1 = u-v from rfl, show openedSites p u v 2 = u from rfl,
    show openedSites p u v 3 = p.1 from rfl, show openedSites p u v 4 = p.2.1 from rfl,
    show openedSites p u v 5 = p.2.2 from rfl,shortGapScore,uncontractedField]
  ring_nf

/-- Both the starting point and every coordinatewise contraction to the floor are feasible. -/
theorem contract_feasible {p : Point} {u v a b : ℝ}
    (h₁ : 1/1000 ≤ a) (h₂ : a ≤ u) (h₃ : 1/1000 ≤ b) (h₄ : b ≤ v)
    (hr : 21/100 ≤ p.1-u) (hz : 21/100 ≤ p.2.1-p.1)
    (ht : 21/100 ≤ p.2.2-p.2.1) (hw : 21/100 ≤ 1-v-p.2.2) :
    Feasible (by decide) (1/1000) (openedSites p a b) := by
  intro i
  fin_cases i <;> norm_num [gap,liftSite,openedSites] <;> linarith

/-- For s=22 and h=1/1000 in the certified capture region, a nonpacked triple
strictly loses against its packed contraction at the same external positions. -/
theorem local_contact_locking {p : Point} {u v : ℝ}
    (hu : u ∈ Icc (1/1000:ℝ) (2/100)) (hv : v ∈ Icc (1/1000:ℝ) (2/100))
    (hr : p.1-u ∈ Icc (21/100:ℝ) (29/100))
    (hz : p.2.1-p.1 ∈ Icc (21/100:ℝ) (29/100))
    (ht : p.2.2-p.2.1 ∈ Icc (21/100:ℝ) (29/100))
    (hw : 1-v-p.2.2 ∈ Icc (21/100:ℝ) (29/100))
    (hn : (u,v) ≠ (1/1000,1/1000)) :
    Feasible (by decide) (1/1000) (openedSites p (1/1000) (1/1000)) ∧
    imageEnergy 22 (openedSites p (1/1000) (1/1000)) < imageEnergy 22 (openedSites p u v) := by
  have hc : CaptureBounds kernel₂ p u v := captureBounds_of_gaps hu.2 hv.2 hr hz ht hw
    (fun _ hx => kernel₂_near hx) (fun _ hx => kernel₂_sides hx)
    (fun _ hx => kernel₂_diagonals hx) kernel₂_one_sub
  have h₂ : ∀ x, HasDerivAt derivKernel (kernel₂ x) x := hasDerivAt_derivKernel
  have he := shortGapScore_lt_packed hasDerivAt_kernel22 h₂ hc (by norm_num : 0<(1/1000:ℝ))
    hu.1 le_rfl hv.1 le_rfl hn
  refine ⟨contract_feasible le_rfl hu.1 le_rfl hv.1 hr.1 hz.1 ht.1 hw.1, ?_⟩
  rw [imageEnergy_lt_iff_pairScore_gt (by decide),openedSites_score,openedSites_score]
  linarith

/-- After fixing the signed first moment and packing the two short gaps, the
four center arcs remain inside the closed strict-concavity domain. -/
theorem localDomain_of_capture {p : Point} {u v : ℝ}
    (hu : u ∈ Icc (1/1000:ℝ) (2/100)) (hv : v ∈ Icc (1/1000:ℝ) (2/100))
    (hr : p.1-u ∈ Icc (21/100:ℝ) (29/100))
    (hz : p.2.1-p.1 ∈ Icc (21/100:ℝ) (29/100))
    (ht : p.2.2-p.2.1 ∈ Icc (21/100:ℝ) (29/100))
    (hw : 1-v-p.2.2 ∈ Icc (21/100:ℝ) (29/100)) : p ∈ localDomain := by
  intro i
  fin_cases i <;> simp only [side, Set.mem_Icc] <;> constructor <;>
    linarith only [hu.1,hu.2,hv.1,hv.2,hr.1,hr.2,hz.1,hz.2,ht.1,ht.2,hw.1,hw.2]

theorem captured_groundState_packed {p : Point} {u v : ℝ}
    (hu : u ∈ Icc (1/1000:ℝ) (2/100)) (hv : v ∈ Icc (1/1000:ℝ) (2/100))
    (hr : p.1-u ∈ Icc (21/100:ℝ) (29/100))
    (hz : p.2.1-p.1 ∈ Icc (21/100:ℝ) (29/100))
    (ht : p.2.2-p.2.1 ∈ Icc (21/100:ℝ) (29/100))
    (hw : 1-v-p.2.2 ∈ Icc (21/100:ℝ) (29/100))
    (hmin : IsGroundState (by decide) (1/1000) 22 (openedSites p u v)) :
    (u,v) = (1/1000,1/1000) ∧ p ∈ localDomain := by
  refine ⟨?_,localDomain_of_capture hu hv hr hz ht hw⟩
  by_contra hn
  obtain ⟨hf,he⟩ := local_contact_locking hu hv hr hz ht hw hn
  exact (not_lt_of_ge (hmin.2 _ hf)) he

#print axioms local_contact_locking
#print axioms captured_groundState_packed
end GaussianChains.Point22
