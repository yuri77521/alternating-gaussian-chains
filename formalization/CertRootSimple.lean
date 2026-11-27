import CertRoot
import CertRootDerivative
import Point22CurvatureCertificate

/-! Simplicity and uniqueness of the scalar root after the triple contacts
are locked. The verified second-derivative boxes cover all of [0.21,0.29]. -/

namespace GaussianChains.Root22
open Set Point22.Curvature

noncomputable def halfSlopePrime (r : ℝ) : ℝ :=
  -packed₂ r - kernel₂ (1/2-r) + 2*kernel₂ (1-2*r)

theorem halfSlope_hasDerivAt (r : ℝ) : HasDerivAt halfSlope (halfSlopePrime r) r := by
  have ha := (hasDerivAt_derivKernel (r-1/1000)).comp r ((hasDerivAt_id r).sub_const (1/1000))
  have hb := hasDerivAt_derivKernel r
  have hc := (hasDerivAt_derivKernel (r+1/1000)).comp r ((hasDerivAt_id r).add_const (1/1000))
  have hd := (hasDerivAt_derivKernel (1/2-r)).comp r ((hasDerivAt_const r (1/2:ℝ)).sub (hasDerivAt_id r))
  have he := (hasDerivAt_derivKernel (1-2*r)).comp r
    ((hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_id r).const_mul 2))
  have H := ((((ha.sub hb).add hc).neg).add hd).sub he
  convert H using 1
  unfold halfSlopePrime packed₂
  change -(curvatureSum (r-1/1000)-curvatureSum r+curvatureSum (r+1/1000)) -
    curvatureSum (1/2-r) + 2*curvatureSum (1-2*r) = _
  ring

theorem halfSlopePrime_lt {r : ℝ} (hr : r ∈ Icc (21/100:ℝ) (29/100)) :
    halfSlopePrime r < -14 := by
  have h1 := packed₂_sides (x := r) ⟨hr.1, by linarith [hr.2]⟩
  have h2 := kernel₂_sides (x := 1/2-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h3 := kernel₂_diagonals (x := 1-2*r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  unfold halfSlopePrime
  linarith

theorem halfSlope_strictAnti : StrictAntiOn halfSlope (Icc (21/100:ℝ) (29/100)) := by
  exact strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (fun r _ => (halfSlope_hasDerivAt r).continuousAt.continuousWithinAt)
    (fun r _ => (halfSlope_hasDerivAt r).hasDerivWithinAt)
    (fun r hr => (halfSlopePrime_lt (interior_subset hr)).trans (by norm_num))

theorem reflection_root_unique_simple :
    ∃ r : ℝ, (lowerRoot:ℝ) < r ∧ r < (upperRoot:ℝ) ∧ halfSlope r = 0 ∧
      deriv halfSlope r < -14 ∧ ∀ y ∈ Icc (21/100:ℝ) (29/100), halfSlope y = 0 → y = r := by
  obtain ⟨r,hl,hu,he⟩ := reflection_root_enclosed
  have hr : r ∈ Icc (21/100:ℝ) (29/100) :=
    ⟨(by norm_num [lowerRoot] : (21/100:ℝ) ≤ (lowerRoot:ℝ)).trans hl.le,
      hu.le.trans (by norm_num [upperRoot])⟩
  refine ⟨r,hl,hu,he,?_, fun y hy hy0 => halfSlope_strictAnti.injOn hy hr (hy0.trans he.symm)⟩
  rw [(halfSlope_hasDerivAt r).deriv]
  exact halfSlopePrime_lt hr

noncomputable def paperForce (r : ℝ) : ℝ :=
  derivKernel (r-1/1000) - derivKernel r + derivKernel (r+1/1000) -
    derivKernel (1/2-r) - derivKernel (2*r)

/-- The same uniqueness, with the sign convention of the printed force (13). -/
theorem paper_force_unique_simple :
    ∃ r : ℝ, (lowerRoot:ℝ) < r ∧ r < (upperRoot:ℝ) ∧ paperForce r = 0 ∧
      14 < deriv paperForce r ∧ ∀ y ∈ Icc (21/100:ℝ) (29/100), paperForce y = 0 → y = r := by
  have hF : paperForce = fun y => -halfSlope y := funext paper_force_eq
  obtain ⟨r,hl,hu,hz,hp,un⟩ := reflection_root_unique_simple
  refine ⟨r,hl,hu,by simp [hF,hz],?_,?_⟩
  · have hneg : HasDerivAt (fun y => -halfSlope y) (-halfSlopePrime r) r :=
      (halfSlope_hasDerivAt r).neg
    rw [hF, hneg.deriv]
    rw [(halfSlope_hasDerivAt r).deriv] at hp
    linarith
  · intro y hy h
    exact un y hy (by simpa [hF] using h)

#print axioms reflection_root_unique_simple
#print axioms paper_force_unique_simple
end GaussianChains.Root22
