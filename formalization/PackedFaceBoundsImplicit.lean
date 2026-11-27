import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-! Real-analytic root germs and their agreement with a uniquely classified threshold.
The parameter need not be interior to the paper's closed nome range. -/

namespace GaussianChains.PackedFace

open Filter Set
open scoped Topology ContDiff

private theorem simpleRootIFT {𝕜 : Type*} [RCLike 𝕜] {n : WithTop ℕ∞}
    {F : 𝕜 × 𝕜 → 𝕜} {q h d : 𝕜} (hn : n ≠ 0)
    (ha : ContDiffAt 𝕜 n F (q,h))
    (hd : HasDerivAt (fun u => F (q,u)) d h) (hne : d ≠ 0) :
    IsContDiffImplicitAt n F (fderiv 𝕜 F (q,h)) (q,h) := by
  let D := fderiv 𝕜 F (q,h)
  let A := D.comp (ContinuousLinearMap.inr 𝕜 𝕜 𝕜)
  have hD : HasFDerivAt F D (q,h) := (ha.differentiableAt hn).hasFDerivAt
  have hA : HasFDerivAt (fun u => F (q,u)) A h :=
    hD.comp h (hasFDerivAt_prodMk_right q h)
  have hone : A 1 = d := hA.hasDerivAt.unique hd
  have hmul (t : 𝕜) : A t = t * d := calc
    A t = A (t • (1:𝕜)) := by simp
    _ = t • A 1 := A.map_smul t 1
    _ = _ := by rw [hone, smul_eq_mul]
  have hbij : Function.Bijective A := by
    constructor
    · intro a b hab
      rw [hmul,hmul] at hab
      exact mul_right_cancel₀ hne hab
    · intro z
      refine ⟨z/d, ?_⟩
      rw [hmul, div_mul_cancel₀ z hne]
  exact ⟨hD, ha, hbij, hn⟩

/-- Continuity of a chosen real root follows from a simple zero and uniqueness in an open
interval. Thus no continuity of the choice operator defining a threshold is needed. -/
theorem continuousWithinAt_root_of_unique {F : ℝ × ℝ → ℝ} {root : ℝ → ℝ}
    {q d : ℝ} {domain interval : Set ℝ} (hinterior : interval ∈ 𝓝 (root q))
    (ha : ContDiffAt ℝ 1 F (q,root q)) (hz : F (q,root q) = 0)
    (hd : HasDerivAt (fun u => F (q,u)) d (root q)) (hne : d ≠ 0)
    (hu : ∀ x ∈ domain, ∀ y ∈ interval, F (x,y) = 0 → y = root x) :
    ContinuousWithinAt root domain q := by
  let I := simpleRootIFT (n := 1) (by decide) ha hd hne
  have heq : I.implicitFunction q = root q :=
    I.eventually_implicitFunction_apply_eq.self_of_nhds rfl
  have hc : ContinuousAt I.implicitFunction q :=
    I.contDiffAt_implicitFunction.continuousAt
  have he : ∀ᶠ x in 𝓝 q, F (x,I.implicitFunction x) = 0 := by
    simpa only [hz] using I.apply_implicitFunction
  have hi : ∀ᶠ x in 𝓝 q, I.implicitFunction x ∈ interval := by
    apply hc
    rwa [heq]
  apply hc.continuousWithinAt.congr_of_eventuallyEq _ heq.symm
  filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds,
    hi.filter_mono nhdsWithin_le_nhds] with x hx he' hi'
  exact (hu x hx _ hi' he').symm

/-- A jointly complex C¹ equation yields a holomorphic implicit branch.  The one-dimensional
holomorphic branch has a real-analytic real part.  Continuity and uniqueness in the
implicit function theorem identify a chosen real root on a possibly closed nome domain. -/
theorem analyticWithinAt_root_complex {F : ℂ × ℂ → ℂ} {root : ℝ → ℝ}
    {q : ℝ} {d : ℂ} {domain : Set ℝ}
    (ha : ContDiffAt ℂ 1 F ((q : ℂ), (root q : ℂ)))
    (hd : HasDerivAt (fun u => F ((q : ℂ),u)) d (root q : ℂ)) (hne : d ≠ 0)
    (hc : ContinuousWithinAt root domain q)
    (he : ∀ᶠ x : ℝ in 𝓝[domain] q, F ((x : ℂ),(root x : ℂ)) = F ((q : ℂ),(root q : ℂ))) :
    AnalyticWithinAt ℝ root domain q := by
  have hift := simpleRootIFT (n := 1) (by decide) ha hd hne
  have hca : AnalyticAt ℂ hift.implicitFunction (q : ℂ) :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr <|
      (hift.contDiffAt_implicitFunction.eventually (by simp)).mono
        (fun _ h => h.differentiableAt (by decide))
  have hra : AnalyticAt ℝ (fun x : ℝ => (hift.implicitFunction x).re) q :=
    (hca.contDiffAt (n := ω)).real_of_complex.analyticAt
  have ht : ContinuousWithinAt (fun x : ℝ => ((x : ℂ), (root x : ℂ))) domain q :=
    Complex.continuous_ofReal.continuousWithinAt.prodMk
      (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hc)
  have hnear := ht.tendsto.eventually hift.eventually_implicitFunction_apply_eq
  apply hra.analyticWithinAt.congr_of_eventuallyEq
  · filter_upwards [hnear,he] with x hx hzero
    exact (congrArg Complex.re (hx hzero)).symm
  · exact (congrArg Complex.re (hift.eventually_implicitFunction_apply_eq.self_of_nhds rfl)).symm

/-- End-to-end version for an endpoint slope. The hypotheses on the real branch are exactly
interior membership, vanishing, simplicity and uniqueness, without a separate regularity
assumption on the chosen branch. -/
theorem analyticWithinAt_simple_real_root {F : ℂ × ℂ → ℂ} {P : ℝ × ℝ → ℝ}
    {root : ℝ → ℝ} {q d : ℝ} {domain interval : Set ℝ}
    (hq : q ∈ domain) (hi : interval ∈ 𝓝 (root q))
    (ha : ContDiffAt ℂ 1 F ((q : ℂ), (root q : ℂ)))
    (hs : ∀ t u : ℝ, F ((t : ℂ),(u : ℂ)) = (P (t,u) : ℂ))
    (hd : HasDerivAt (fun u => P (q,u)) d (root q)) (hne : d ≠ 0)
    (hz : ∀ t ∈ domain, P (t,root t) = 0)
    (hu : ∀ t ∈ domain, ∀ u ∈ interval, P (t,u) = 0 → u = root t) :
    AnalyticWithinAt ℝ root domain q := by
  let C : ℝ × ℝ → ℂ × ℂ := fun p => ((p.1 : ℂ), (p.2 : ℂ))
  have hC : ContDiffAt ℝ 1 C (q,root q) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_fst).prodMk
      (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_snd)
  have hP : ContDiffAt ℝ 1 P (q,root q) := by
    have hcomp := Complex.reCLM.contDiff.contDiffAt.comp (q,root q)
      ((ha.restrict_scalars ℝ).comp (q,root q) hC)
    simpa [Function.comp_def, C, hs] using hcomp
  have hc := continuousWithinAt_root_of_unique hi hP (hz q hq) hd hne hu
  let f : ℂ → ℂ := fun u => F ((q : ℂ),u)
  have hdiff : DifferentiableAt ℂ f (root q : ℂ) :=
    (ha.differentiableAt (by decide)).comp _ (hasFDerivAt_prodMk_right _ _).differentiableAt
  have hreal : (deriv f (root q : ℂ)).re = d := by
    apply HasDerivAt.unique _ hd
    simpa [f, hs] using hdiff.hasDerivAt.real_of_complex
  refine analyticWithinAt_root_complex ha hdiff.hasDerivAt ?_ hc ?_
  · intro he
    apply hne
    rw [← hreal, he, Complex.zero_re]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hs, hs, hz t ht, hz q hq]

end GaussianChains.PackedFace
