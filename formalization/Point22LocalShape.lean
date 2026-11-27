import Point22Score
import Point22Orbits
import Point22CurvatureCertificate
import CertRoot
import CertRootDerivative

/-! Unique minimum in the complete certified four-center domain, at the actual
width and gap floor. This proof uses the certified derivative intervals and root. -/

namespace GaussianChains.Point22
open Root22 Set

private theorem field_deriv {G D : ℝ → ℝ} (hd : ∀ x, HasDerivAt G (D x) x) (h x : ℝ) :
    HasDerivAt (tripleField G h) (tripleField D h x) x := by
  simpa [tripleField,Function.comp_def] using
    ((((hd (x-h)).comp x ((hasDerivAt_id x).sub_const h)).sub (hd x)).add
      ((hd (x+h)).comp x ((hasDerivAt_id x).add_const h)))

theorem strict_local_shape {R : ℝ} (hl : (lowerRoot:ℝ) < R) (hu : R < (upperRoot:ℝ))
    (he : derivKernel (R-1/1000)-derivKernel R+derivKernel (R+1/1000)-
      derivKernel (1/2-R)-derivKernel (2*R) = 0)
    {p : Point} (hp : p ∈ localDomain) (hneq : p ≠ (R,1/2,1-R)) :
    imageEnergy 22 (sites (1/1000) R) < imageEnergy 22 (cell3111 (1/1000) p) := by
  have h₁ := field_deriv hasDerivAt_kernel22 (1/1000)
  have h₂ := field_deriv hasDerivAt_derivKernel (1/1000)
  have hsym := derivative_reflection h₁ (tripleField_reflect 22 (1/1000))
  have hcrit := (fixed_line_force_iff derivKernel_one_sub hsym R).2 he
  have hR : (R,1/2,1-R) ∈ localDomain := by
    have hr0 : (24/100:ℝ) < R := lt_trans (by norm_num [lowerRoot]) hl
    have hr1 : R < 26/100 := lt_trans hu (by norm_num [upperRoot])
    intro i
    fin_cases i <;> simp [side] <;> constructor <;> linarith
  have H := stationary_score_strict_max hasDerivAt_kernel22 h₁ hasDerivAt_derivKernel h₂
    (fun _ hp => Curvature.certifiedBounds hp) hR hp hneq.symm hcrit
  change imageEnergy 22 (cell3111 (1/1000) (R,1/2,1-R)) < _
  rw [cell3111_energy,cell3111_energy]
  linarith

theorem unique_captured_minimum :
    ∃ R : ℝ, (lowerRoot:ℝ) < R ∧ R < (upperRoot:ℝ) ∧
      ∀ p ∈ localDomain, p ≠ (R,1/2,1-R) →
      imageEnergy 22 (sites (1/1000) R) < imageEnergy 22 (cell3111 (1/1000) p) := by
  obtain ⟨R,hl,hu,he⟩ := paper_force_root_enclosed
  exact ⟨R,hl,hu,fun _ => strict_local_shape hl hu he⟩


#print axioms unique_captured_minimum

end GaussianChains.Point22

