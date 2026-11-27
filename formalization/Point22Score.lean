import Point22SixScore
import ChainScore
import Point22Hessian
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! The local score of the triple and three singletons is an exact restriction
of the energy of six physical sites, including the triple's internal score. -/

noncomputable section
namespace GaussianChains.Point22

def tripleField (G : ℝ → ℝ) (h d : ℝ) := G (d-h) - G d + G (d+h)

def cell3111 (h : ℝ) (p : Point) : Fin 6 → ℝ := ![-h,0,h,p.1,p.2.1,p.2.2]

set_option maxHeartbeats 2000000 in
theorem cell3111_score (s h : ℝ) (p : Point) :
    pairScore s (cell3111 h p) =
    kernel s (2*h) - 2 * kernel s h + variableScore (kernel s) (tripleField (kernel s) h) p := by
  rw [six_score_terms]
  generalize kernel s = G
  simp only [show cell3111 h p 0 = -h from rfl, show cell3111 h p 1 = 0 from rfl,
    show cell3111 h p 2 = h from rfl, show cell3111 h p 3 = p.1 from rfl,
    show cell3111 h p 4 = p.2.1 from rfl, show cell3111 h p 5 = p.2.2 from rfl,
    variableScore,tripleField]
  ring_nf

theorem cell3111_energy (s h : ℝ) (p : Point) :
    imageEnergy s (cell3111 h p) =
    1 - kernel s 0 - (kernel s (2*h) - 2 * kernel s h +
      variableScore (kernel s) (tripleField (kernel s) h) p)/3 := by
  rw [imageEnergy_eq_pairScore (by decide), cell3111_score]
  push_cast
  ring

def reflectCenters (p : Point) : Point := (1-p.2.2,1-p.2.1,1-p.1)

theorem reflectCenters_fixed_iff (p : Point) :
    reflectCenters p = p ↔ p.2.1 = 1/2 ∧ p.2.2 = 1-p.1 := by
  rcases p with ⟨r,z,t⟩
  simp [reflectCenters, Prod.ext_iff]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by linarith,by linarith,by linarith⟩

theorem kernel_reflect (s d : ℝ) : kernel s (1-d) = kernel s d := by
  rw [show 1-d = -d+(1:ℤ) by push_cast; ring, kernel_add_int, kernel_neg]

theorem tripleField_reflect (s h d : ℝ) :
    tripleField (kernel s) h (1-d) = tripleField (kernel s) h d := by
  unfold tripleField
  rw [show 1-d-h=1-(d+h) by ring, show 1-d+h=1-(d-h) by ring]
  simp only [kernel_reflect]
  ring

theorem reflectCenters_preserves_score (s h : ℝ) (p : Point) :
    variableScore (kernel s) (tripleField (kernel s) h) (reflectCenters p) =
    variableScore (kernel s) (tripleField (kernel s) h) p := by
  simp only [variableScore, reflectCenters, tripleField_reflect]
  ring_nf

/-- The exact fixed-line score as a univariate function. -/
theorem fixedLine_score (s h R : ℝ) :
    variableScore (kernel s) (tripleField (kernel s) h) (R,1/2,1-R) =
    -2*tripleField (kernel s) h R + tripleField (kernel s) h (1/2) -
      2*kernel s (1/2-R) + kernel s (1-2*R) := by
  simp only [variableScore, tripleField_reflect]
  rw [show 1-R-R = 1-2*R by ring, show 1-R-1/2 = 1/2-R by ring]
  ring

/-- The completion of the square used for the nine words with disjoint contacts. -/
theorem disjoint_pair_lower_bound {E E₀ K h δ : ℝ}
    (hE : E₀ + δ^2/6 - 2*K*h*δ/3 - 2*K*h^2/3 ≤ E) :
    E₀ - (2*K^2+2*K)*h^2/3 ≤ E := by
  linarith [sq_nonneg (δ-2*K*h)]

end GaussianChains.Point22




