import PackedFaceBoundsComplexBridge
import PackedFaceModesNormal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-! Joint complex regularity of both endpoint-slope functions before implicit inversion. -/
noncomputable section
namespace GaussianChains.PackedFace
open Filter
open scoped Topology

/-- The complex endpoint equation, with z determined by the selected edge. -/
def complexEndpoint (z : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  ∑' k : ℕ, complexSlopeMode (k+1) p.1 p.2 (z p.2)

/-- A jointly holomorphic parametrization may vary all three arguments of
the endpoint equation. Its restriction to the polydisc is jointly complex C¹. -/
theorem complexSlopeMap_contDiffAt {Q X Z : (ℂ × ℂ) → ℂ}
    (hQ : ContDiff ℂ 1 Q) (hX : ContDiff ℂ 1 X) (hZ : ContDiff ℂ 1 Z)
    (a : ℂ × ℂ) (hq : ‖Q a‖ < 1/2) (hx : ‖X a‖ < 2) (haz : ‖Z a‖ < 2) :
    ContDiffAt ℂ 1 (fun p => ∑' k : ℕ, complexSlopeMode (k+1) (Q p) (X p) (Z p)) a := by
  apply joint_contDiffAt_tsum (v := fun k => slopeMajorant (k+1))
  · intro k
    have hT : ContDiff ℂ 1 (fun p : ℂ × ℂ => (Polynomial.Chebyshev.T ℂ (k+1 : ℕ)).eval (X p)) :=
      (Polynomial.Chebyshev.T ℂ (k+1 : ℕ)).differentiable.contDiff.comp hX
    have hU : ContDiff ℂ 1 (fun p : ℂ × ℂ =>
        (Polynomial.Chebyshev.U ℂ (((k+1 : ℕ) : ℤ)-1)).eval (Z p)) :=
      (Polynomial.Chebyshev.U ℂ (((k+1 : ℕ) : ℤ)-1)).differentiable.contDiff.comp hZ
    unfold complexSlopeMode
    fun_prop
  · exact (summable_nat_add_iff 1).mpr summable_slopeMajorant
  · have h1 : ∀ᶠ p in 𝓝 a, ‖Q p‖ < 1/2 :=
      hQ.continuous.norm.continuousAt.eventually_lt continuousAt_const hq
    have h2 : ∀ᶠ p in 𝓝 a, ‖X p‖ < 2 :=
      hX.continuous.norm.continuousAt.eventually_lt continuousAt_const hx
    have h3 : ∀ᶠ p in 𝓝 a, ‖Z p‖ < 2 :=
      hZ.continuous.norm.continuousAt.eventually_lt continuousAt_const haz
    filter_upwards [h1, h2, h3] with p h1p h2p h3p
    exact fun n => norm_complexSlopeMode_le (n+1) h1p.le h2p.le h3p.le

/-- Joint complex C¹ on the open polydisc, including nonconstant endpoint abscissae. -/
theorem complexEndpoint_contDiffAt {z : ℂ → ℂ} (hz : ContDiff ℂ 1 z)
    (a : ℂ × ℂ) (hq : ‖a.1‖ < 1/2) (hx : ‖a.2‖ < 2) (haz : ‖z a.2‖ < 2) :
    ContDiffAt ℂ 1 (complexEndpoint z) a :=
  complexSlopeMap_contDiffAt contDiff_fst contDiff_snd (hz.comp contDiff_snd) a hq hx haz

/-- Complexification agrees with the actual real endpoint-slope series on the
whole real slice, without any conditional-summation convention. -/
theorem complexEndpoint_ofReal {z : ℂ → ℂ} {g : ℝ → ℝ}
    (hz : ∀ x : ℝ, z (x : ℂ) = (g x : ℂ)) (q x : ℝ) :
    complexEndpoint z (q, x) = (endpointSlope q x (g x) : ℂ) := by
  rw [complexEndpoint, ofReal_endpointSlope, hz]

/-- Joint C¹ for the slope as a function of nome and gap (floor), the actual
variables of the implicit curves. -/
def complexFloorSlope (z : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  complexEndpoint z (p.1, Complex.cos (2*(Real.pi:ℂ)*p.2))

theorem complexFloorSlope_contDiffAt {z : ℂ → ℂ} (hz : ContDiff ℂ 1 z)
    {a : ℂ × ℂ} (hq : ‖a.1‖ < 1/2)
    (hx : ‖Complex.cos (2*(Real.pi:ℂ)*a.2)‖ < 2)
    (haz : ‖z (Complex.cos (2*(Real.pi:ℂ)*a.2))‖ < 2) :
    ContDiffAt ℂ 1 (complexFloorSlope z) a :=
  (complexEndpoint_contDiffAt hz (a.1, Complex.cos (2*(Real.pi:ℂ)*a.2)) hq hx haz).comp
    (f := fun p : ℂ × ℂ => (p.1, Complex.cos (2*(Real.pi:ℂ)*p.2))) a (by fun_prop)

theorem complexFloorSlope_ofReal {z : ℂ → ℂ} {g : ℝ → ℝ}
    (hz : ∀ x : ℝ, z (x : ℂ) = (g x : ℂ)) (q h : ℝ) :
    complexFloorSlope z (q,h) =
      (endpointSlope q (Real.cos (2*Real.pi*h)) (g (Real.cos (2*Real.pi*h))) : ℂ) := by
  unfold complexFloorSlope
  simpa using complexEndpoint_ofReal hz q (Real.cos (2*Real.pi*h))

/-- At real gaps both endpoint abscissae lie inside the complex domain, for
the entire range of nomes in Theorem 3. The outer cubic is minus the cosine
of the triple angle, so it stays in the unit interval in absolute value. -/
theorem both_complexFloorSlopes_contDiffAt {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ 17/50) (h : ℝ) :
    ContDiffAt ℂ 1 (complexFloorSlope (fun _ => 1)) ((q : ℂ), (h : ℂ)) ∧
      ContDiffAt ℂ 1 (complexFloorSlope (fun x => 3*x-4*x^3)) ((q : ℂ), (h : ℂ)) := by
  let θ := 2*Real.pi*h
  have he : Complex.cos (2*(Real.pi:ℂ)*(h:ℂ)) = (Real.cos θ : ℂ) := by
    simp [θ]
  have hc : ‖Complex.cos (2*(Real.pi:ℂ)*(h:ℂ))‖ < 2 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩]
  have hq' : ‖(q:ℂ)‖ < 1/2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    linarith
  refine ⟨complexFloorSlope_contDiffAt contDiff_const hq' hc (by norm_num),
    complexFloorSlope_contDiffAt (by fun_prop) hq' hc ?_⟩
  rw [he]
  have hy : 3*(Real.cos θ : ℂ)-4*(Real.cos θ : ℂ)^3 = (-(Real.cos (3*θ)) : ℝ) := by
    rw [Real.cos_three_mul]
    push_cast
    ring
  rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  linarith [abs_le.mpr ⟨Real.neg_one_le_cos (3*θ), Real.cos_le_one (3*θ)⟩]

/-- A nonzero derivative on the real floor slice is the same derivative in the
complex implicit function theorem. This uses uniqueness of derivatives, including
the imaginary component of the complex derivative. -/
theorem complexFloorSlope_floor_deriv {z : ℂ → ℂ} {g : ℝ → ℝ} {q h d : ℝ}
    (hz : ∀ x : ℝ, z (x : ℂ) = (g x : ℂ))
    (hc : ContDiffAt ℂ 1 (complexFloorSlope z) ((q : ℂ), (h : ℂ)))
    (hd : HasDerivAt (fun u : ℝ =>
      endpointSlope q (Real.cos (2*Real.pi*u)) (g (Real.cos (2*Real.pi*u)))) d h) :
    HasDerivAt (fun u : ℂ => complexFloorSlope z ((q : ℂ),u)) (d : ℂ) (h : ℂ) := by
  have hC := (hc.differentiableAt one_ne_zero).comp (h : ℂ)
    (hasFDerivAt_prodMk_right (q : ℂ) (h : ℂ)).differentiableAt
  have hf : DifferentiableAt ℂ (fun u : ℂ => complexFloorSlope z ((q : ℂ),u)) (h : ℂ) := hC
  have hreal : HasDerivAt (fun u : ℝ => complexFloorSlope z ((q : ℂ),(u : ℂ))) (d : ℂ) h := by
    simpa only [complexFloorSlope_ofReal hz] using hd.ofReal_comp
  rw [← hf.hasDerivAt.comp_ofReal.unique hreal]
  exact hf.hasDerivAt

#print axioms complexFloorSlope_contDiffAt

end GaussianChains.PackedFace


