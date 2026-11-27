import BifurcationPhysical
import Mathlib.Topology.Order.LocalExtr

/-! Off-face directions, uniformly as h crosses the critical floor. -/
noncomputable section
namespace GaussianChains.Bifurcation
open Filter Set
open scoped Topology

private theorem near_partial {h₀ : ℝ} (hp : 0 < h₀) (h6 : h₀ < 1/6) :
    ∃ r > (0:ℝ), ∃ γ > (0:ℝ), ∀ h t (u : Release), |h-h₀| < r → |t| < r → ‖u‖ < r →
      DifferentiableAt ℝ (fun v => imageEnergy 8 (Release.sites h t v)) u ∧
      ∀ j : Fin 4, γ ≤ fderiv ℝ (fun v => imageEnergy 8 (Release.sites h t v)) u (Pi.single j 1) := by
  let F := fun p : ℝ × ℝ × Release => imageEnergy 8 (Release.sites p.1 p.2.1 p.2.2)
  have hf : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.mpr
    fun p => (Release.chartEnergy_analyticAt (by norm_num : (0:ℝ)<8) p).contDiffAt
  let lift : Release →L[ℝ] ℝ × ℝ × Release :=
    (0 : Release →L[ℝ] ℝ).prod ((0 : Release →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Release))
  let D := fun (p : ℝ × ℝ × Release) => (fderiv ℝ F p).comp lift
  have hD (h t : ℝ) (u : Release) : HasFDerivAt
      (fun v => imageEnergy 8 (Release.sites h t v)) (D (h,t,u)) u := by
    have hi : HasFDerivAt (fun v : Release => (h,t,v)) lift u :=
      (hasFDerivAt_const (𝕜 := ℝ) h u).prodMk ((hasFDerivAt_const t u).prodMk (hasFDerivAt_id u))
    exact (hf.differentiable (by norm_num) (h,t,u)).hasFDerivAt.comp u hi
  let γ := deriv (fun h => imageEnergy 8 (PackedFace.sites h 0)) h₀ / 8
  have hγ : 0 < γ := div_pos (centered_image_deriv_pos (by norm_num) exp_width_eight hp h6) (by norm_num)
  have H : ∀ᶠ p : ℝ × ℝ × Release in 𝓝 (h₀,0,0), ∀ j : Fin 4, γ < D p (Pi.single j 1) := by
    apply Filter.eventually_all.mpr
    intro j
    have he : Continuous (fun p => D p (Pi.single j 1)) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := lift (Pi.single j 1)))
    apply he.continuousAt.eventually (lt_mem_nhds ?_)
    change γ < D (h₀,0,0) (Pi.single j 1)
    rw [← (hD h₀ 0 0).fderiv, Release.gaussian_release_partial (by norm_num)]
    dsimp [γ] at hγ ⊢
    linarith only [hγ]
  obtain ⟨r,hr,Hr⟩ := Metric.eventually_nhds_iff.mp H
  refine ⟨r,hr,γ,hγ,?_⟩
  intro h t u hh ht hu
  refine ⟨(hD h t u).differentiableAt,?_⟩
  intro j
  rw [(hD h t u).fderiv]
  apply le_of_lt (Hr (y := (h,t,u)) _ j)
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, dist_zero_right, max_lt_iff]
  exact ⟨hh,ht,hu⟩

private theorem scaled_lt {u : Release} {r a : ℝ} (ha : a ∈ Icc 0 1) (hu : ‖u‖ < r) :
    ‖a • u‖ < r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha.2).trans_lt hu

theorem uniform_face_lower {h₀ : ℝ} (hp : 0 < h₀) (h6 : h₀ < 1/6) :
    ∃ r > (0:ℝ), ∀ h t (u : Release), |h-h₀| < r → |t| < r → ‖u‖ < r →
      (∀ i, 0 ≤ u i) → imageEnergy 8 (PackedFace.sites h t) ≤ imageEnergy 8 (Release.sites h t u) := by
  obtain ⟨r,hr,γ,hγ,H⟩ := near_partial hp h6
  refine ⟨r,hr,?_⟩
  intro h t u hh ht hu hpos
  have he := release_segment _ u zero_lt_one hpos
    (fun a ha => (H h t _ hh ht (scaled_lt ha hu)).1)
    (fun a ha => (H h t _ hh ht (scaled_lt (Ioo_subset_Icc_self ha) hu)).2)
  simp only [sub_zero, one_mul, zero_smul, Release.zero_release_sites] at he
  linarith [mul_nonneg hγ.le (Finset.sum_nonneg (s := Finset.univ) fun i _ => hpos i)]

/-- A nonzero release cannot be a local minimum near a centered width-eight
cell. The neighborhood is uniform in h and t. Every smaller point produced here
has the same h,t, satisfies all six floor constraints, and approaches the given
chart point as the contraction parameter tends to one. -/
theorem no_off_face_minima_near {h₀ : ℝ} (hp : 0 < h₀) (h6 : h₀ < 1/6) :
    ∃ r > (0:ℝ), ∀ h t (u : Release), |h-h₀| < r → |t| < r → ‖u‖ < r →
      (∀ i, h ≤ Release.gaps (Release.sites h t u) i) → u ≠ 0 →
      ∀ ε > (0:ℝ), ∃ a ∈ Ioo (0:ℝ) 1, 1-a < ε ∧
        (∀ i, h ≤ Release.gaps (Release.sites h t (a • u)) i) ∧
        imageEnergy 8 (Release.sites h t (a • u)) < imageEnergy 8 (Release.sites h t u) := by
  obtain ⟨r,hr,γ,hγ,H⟩ := near_partial hp h6
  refine ⟨r,hr,?_⟩
  intro h t u hh ht hu hF hne ε hε
  obtain ⟨hu₀,H₁,H₂⟩ := (Release.feasible_iff h t u).mp hF
  obtain ⟨a,ha,haε,he⟩ := smaller_release _ hγ hu₀ hne
    (fun a ha => (H h t _ hh ht (scaled_lt ha hu)).1)
    (fun a ha => (H h t _ hh ht (scaled_lt (Ioo_subset_Icc_self ha) hu)).2) ε hε
  refine ⟨a,ha,haε,(Release.feasible_iff h t _).mpr ?_,he⟩
  have haU (i : Fin 4) : (a • u) i ≤ u i :=
    mul_le_of_le_one_left (hu₀ _) ha.2.le
  exact ⟨fun i => mul_nonneg ha.1.le (hu₀ i), by linarith [haU 0,haU 1], by linarith [haU 2,haU 3]⟩

/-- Full-simplex local minimizers in the neighborhood lie on the packed face. -/
theorem localMin_implies_packed {h₀ : ℝ} (hp : 0 < h₀) (h6 : h₀ < 1/6) :
    ∃ r > (0:ℝ), ∀ h t (u : Release), |h-h₀| < r → |t| < r → ‖u‖ < r →
      (∀ i, h ≤ Release.gaps (Release.sites h t u) i) →
      IsLocalMinOn (fun p : ℝ × Release => imageEnergy 8 (Release.sites h p.1 p.2))
        {p | ∀ i, h ≤ Release.gaps (Release.sites h p.1 p.2) i} (t,u) → u=0 := by
  obtain ⟨r,hr,Hr⟩ := no_off_face_minima_near hp h6
  refine ⟨r,hr,?_⟩
  intro h t u hh ht hu hF hM
  by_contra hn
  obtain ⟨e,he,He⟩ := Metric.mem_nhdsWithin_iff.mp hM
  have hpos : 0 < ‖u‖ + 1 := by positivity
  obtain ⟨a,ha,hae,hf,hdown⟩ := Hr h t u hh ht hu hF hn _ (div_pos he hpos)
  have hd : dist (a • u) u < e := by
    rw [dist_eq_norm,show a • u-u=(a-1) • u by rw [sub_smul,one_smul],norm_smul,
      Real.norm_eq_abs,abs_of_neg (sub_neg.mpr ha.2)]
    have ht' := (lt_div_iff₀ hpos).1 hae
    nlinarith [norm_nonneg u, sub_pos.mpr ha.2]
  have H := He (show (t,a•u) ∈ Metric.ball (t,u) e ∩
        {p : ℝ × Release | ∀ i, h ≤ Release.gaps (Release.sites h p.1 p.2) i} by
    refine ⟨?_,hf⟩
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using hd)
  exact (not_le_of_gt hdown) H

end GaussianChains.Bifurcation
