import Bifurcation
import BifurcationCenter
import BifurcationRelease
import PackedFaceModesEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-! The centered slope and the four inward variations for the physical six-site energy. -/
noncomputable section
namespace GaussianChains.Bifurcation
open PackedFace

theorem centeredFourier_imageEnergy {s : ℝ} (hs : 0 < s) (h : ℝ) :
    imageEnergy s (sites h 0) =
      centeredFourier (Real.exp (-(Real.pi^2)/s)) (Real.sqrt (Real.pi/s)) h := by
  let q := Real.exp (-(Real.pi^2)/s)
  let w (k : ℕ) := q^((k+1)^2) * ‖structureFactor (sites h 0) (k+1)‖^2
  have hw : Summable w := fourier_summable _ hs
  have hev : Summable (fun k => w (2*k)) :=
    hw.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hod : Summable (fun k => w (2*k+1)) :=
    hw.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have h₁ (k : ℕ) : w (2*k) =
      4 * (q^((oddMode k)^2) * (2*Real.cos (oddMode k*(2*Real.pi*h))-1)^2) := by
    dsimp [w, oddMode]
    rw [structureFactor_sites_sq, amplitude_eq_cos]
    simp only [mul_zero, Real.cos_zero, mul_one, pow_succ, pow_mul]
    norm_num
    ring
  have h₂ (k : ℕ) : w (2*k+1) = 0 := by
    dsimp [w]
    rw [structureFactor_sites_sq]
    simp only [mul_zero, Real.cos_zero, mul_one, pow_succ, pow_mul]
    norm_num
  have heq := tsum_even_add_odd hev hod
  simp only [h₁, h₂, tsum_zero, add_zero, tsum_mul_left] at heq
  rw [imageEnergy_fourier 3 hs]
  change 1-2*Real.sqrt (Real.pi/s)/6*(∑' k, w k) = _
  rw [← heq]
  unfold centeredFourier
  dsimp [q]
  ring

theorem centered_image_deriv_pos {s h : ℝ} (hs : 0 < s)
    (hq : Real.exp (-(Real.pi^2)/s) ≤ 1/2) (hh : 0 < h) (hh' : h < 1/6) :
    0 < deriv (fun v => imageEnergy s (sites v 0)) h := by
  have he : (fun v => imageEnergy s (sites v 0)) =
      centeredFourier (Real.exp (-(Real.pi^2)/s)) (Real.sqrt (Real.pi/s)) :=
    funext (centeredFourier_imageEnergy hs)
  rw [he]
  exact centeredFourier_deriv_pos (Real.exp_pos _) hq (by positivity) hh hh'

theorem exp_width_eight : Real.exp (-(Real.pi^2)/8) ≤ 1/2 := by
  rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith [Real.add_one_le_exp (Real.pi^2/8), Real.pi_gt_d2,
    mul_pos (sub_pos.mpr Real.pi_gt_d2) Real.pi_pos]

/-- Opening any one of the four contacts at t=0 has positive derivative
throughout the open packed branch at width eight, including its critical floor. -/
theorem release_partial_pos_width_eight {h : ℝ} (hh : 0 < h) (hh' : h < 1/6) (j : Fin 4) :
    0 < deriv (fun z => imageEnergy 8 (Release.sites h 0 (fun i => if i = j then z else 0))) 0 := by
  rw [(Release.gaussian_four_release_derivatives 8 (by norm_num) h j).deriv]
  exact div_pos (centered_image_deriv_pos (by norm_num) exp_width_eight hh hh') (by norm_num)

/-- A single positive lower bound works for all four releases in a common
neighborhood of any centered cell with 0<h<1/6. -/
theorem uniform_release_width_eight {h : ℝ} (hh : 0 < h) (hh' : h < 1/6) :
    ∃ γ > (0:ℝ), ∃ r > (0:ℝ), ∀ t u, |t| < r → ‖u‖ < r → (∀ i, 0 ≤ u i) →
      γ * (∑ i, u i) ≤ imageEnergy 8 (Release.sites h t u) -
        imageEnergy 8 (sites h t) := by
  let F := fun p : ℝ × Release => imageEnergy 8 (Release.sites h p.1 p.2)
  have hf : ContDiff ℝ 1 F := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact ((Release.chartEnergy_analyticAt (by norm_num : (0:ℝ)<8) (h,p)).comp
      (analyticAt_const.prod analyticAt_id)).contDiffAt
  let D := fun t u => (fderiv ℝ F (t,u)).comp (ContinuousLinearMap.inr ℝ ℝ Release)
  have hD (t : ℝ) (u : Release) : HasFDerivAt
      (fun v => F (t,v)) (D t u) u := by
    exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp u
      ((hasFDerivAt_const t u).prodMk (hasFDerivAt_id u))
  let g := deriv (fun v => imageEnergy 8 (sites v 0)) h / 4
  have hg : 0 < g := div_pos (centered_image_deriv_pos (by norm_num) exp_width_eight hh hh')
    (by norm_num)
  have slope (j : Fin 4) : D 0 0 (Pi.single j 1) = g := by
    rw [← (hD 0 0).fderiv]
    exact Release.gaussian_release_partial (by norm_num) h j
  have hcont (j : Fin 4) : ContinuousAt
      (fun p : ℝ × Release => D p.1 p.2 (Pi.single j 1)) (0,0) := by
    exact ((hf.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := (0, (Pi.single j 1 : Release))))).continuousAt
  refine ⟨g/2, by positivity, ?_⟩
  obtain ⟨r,hr,Hu⟩ := uniform_release_neighborhood (fun t u => F (t,u)) D hD hcont
    (fun j => by rw [slope j]; linarith : ∀ j, g/2 < D 0 0 (Pi.single j 1))
  refine ⟨r,hr,?_⟩
  intro t u ht hu hu'
  simpa [F, Release.zero_release_sites] using Hu t u ht hu hu'

/-- A strict face minimum of the centered cell lifts to the full constrained
gap simplex at width eight. The chart pins site zero, removing translations. -/
theorem strict_full_of_strict_face {h : ℝ} (hh : 0 < h) (hh' : h < 1/6)
    (hface : ∃ d>0, ∀ t, |t| < d → t ≠ 0 →
      imageEnergy 8 (sites h 0) < imageEnergy 8 (sites h t)) :
    ∃ r>0, ∀ t u, |t| < r → ‖u‖ < r →
      (∀ i, h ≤ Release.gaps (Release.sites h t u) i) → (t ≠ 0 ∨ u ≠ 0) →
      imageEnergy 8 (sites h 0) < imageEnergy 8 (Release.sites h t u) := by
  obtain ⟨d,hd,Hd⟩ := hface
  obtain ⟨γ,hγ,r,hr,Hr⟩ := uniform_release_width_eight hh hh'
  refine ⟨min d r,lt_min hd hr,?_⟩
  intro t u ht hu hf hn
  have hu' := ((Release.feasible_iff h t u).mp hf).1
  have he := Hr t u (ht.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _)) hu'
  rcases eq_or_ne t 0 with rfl|h
  · have hp := mul_pos hγ (total_release_pos hu' (hn.resolve_left (not_not_intro rfl)))
    linarith
  · have hsmall := Hd t (ht.trans_le (min_le_left _ _)) h
    have hnonneg : 0 ≤ γ * ∑ i, u i := mul_nonneg hγ.le (Finset.sum_nonneg fun i _ => hu' i)
    linarith

/-- A descending face direction and an ascending contact direction give points
of strictly opposite energy on the feasible simplex in every chart neighborhood. -/
theorem full_saddle_of_face_descent {h : ℝ} (hh : 0 < h) (hh' : h < 1/6)
    (hface : ∀ d>0, ∃ t, |t| < d ∧ feasible h t ∧
      imageEnergy 8 (sites h t) < imageEnergy 8 (sites h 0)) :
    ∀ ε>0, ∃ t u, |t| < ε ∧ ‖u‖ < ε ∧
      (∀ i, h ≤ Release.gaps (Release.sites h t 0) i) ∧
      (∀ i, h ≤ Release.gaps (Release.sites h 0 u) i) ∧
      imageEnergy 8 (Release.sites h t 0) < imageEnergy 8 (sites h 0) ∧
      imageEnergy 8 (sites h 0) < imageEnergy 8 (Release.sites h 0 u) := by
  intro ε hε
  obtain ⟨t,ht,hft,hlt⟩ := hface ε hε
  obtain ⟨γ,hγ,r,hr,Hr⟩ := uniform_release_width_eight hh hh'
  let a := min (min (ε/2) (r/2)) ((1/2-3*h)/4)
  have ha : 0 < a := lt_min (lt_min (by positivity) (by positivity)) (by linarith)
  have has := min_le_right (min (ε/2) (r/2)) ((1/2-3*h)/4)
  have hae : a < ε := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have har : a < r := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  let u : Release := fun _ => a
  have hnorm : ‖u‖ = a := by simp [u, Real.norm_eq_abs, abs_of_pos ha]
  have he := Hr 0 u (by simpa using hr) (hnorm ▸ har) (fun _ => ha.le)
  have hp : 0 < γ * ∑ i, u i := by simpa [u] using mul_pos hγ (show 0 < (4:ℝ)*a by positivity)
  refine ⟨t,u,ht,hnorm ▸ hae,?_,?_,?_,by linarith⟩
  · apply (Release.feasible_iff _ _ _).mpr
    have hft' := abs_le.mp hft
    dsimp [bound] at hft'
    simpa using And.intro (show 3*h ≤ 1/2+t by linarith [hft'.1])
      (show 3*h ≤ 1/2-t by linarith [hft'.2])
  · apply (Release.feasible_iff _ _ _).mpr
    refine ⟨fun _ => ha.le,?_,?_⟩ <;> change 3*h + a + a ≤ _ <;> dsimp [a] at * <;> linarith
  · simpa [Release.zero_release_sites] using hlt

end GaussianChains.Bifurcation
