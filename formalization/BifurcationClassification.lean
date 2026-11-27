import BifurcationPhysical
import PackedFaceEnergyTable
import PackedFaceCurvatureSigns

/-! The two centered-branch conclusions of Proposition 4 on the full gap simplex.
The signed displacement can approach zero from either side; increasing a contact
is allowed only in the nonnegative release orthant. -/
noncomputable section
namespace GaussianChains.Bifurcation
open Set Filter PackedFace
open scoped Topology

/-- The width-eight nome lies in the full closed-face parameter range. -/
theorem nome_eight_le_faceQ : Real.exp (-(Real.pi^2)/8) ≤ faceQ := by
  have hx : 61/50 ≤ Real.pi^2/8 := by nlinarith [Real.pi_gt_d2, sq_nonneg (Real.pi-3.14)]
  have e := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (61/50 : ℝ)) 3
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at e
  calc
    _ ≤ Real.exp (-(61/50 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp (61/50 : ℝ) := by rw [Real.exp_neg, one_div]
    _ ≤ _ := (div_le_iff₀ (Real.exp_pos _)).mpr (by unfold faceQ; linarith)

/-- A negative derivative at the left endpoint supplies lower energies at
arbitrarily small positive squared displacement, without an interior claim. -/
private theorem arbitrarily_small_decrease {F : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivWithinAt F a (Icc 0 2) 0) (ha : a < 0) {y : ℝ} (hy : 0 < y) :
    ∃ z ∈ Ioo 0 y, F z < F 0 := by
  have hi := hd.mono (Ioo_subset_Icc_self : Ioo (0 : ℝ) 2 ⊆ Icc 0 2)
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioo 0 2)).mp hi
  rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0:ℝ)<2)] at ht
  have hyv : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ∈ Ioo 0 y := Ioo_mem_nhdsGT hy
  obtain ⟨z, hz, hz'⟩ := (hyv.and (ht.eventually_lt_const ha)).exists
  rw [slope_def_field, sub_zero, div_neg_iff] at hz'
  exact ⟨z, hz, sub_neg.mp (hz'.resolve_left (fun h => (not_lt_of_gt hz.1) h.2)).1⟩

private theorem descent_of_negative_slope {s h : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ faceQ) (hh : 0 < h) (h6 : h < 1/6)
    (hneg : phiD (Real.exp (-(Real.pi^2)/s)) h 0 < 0) :
    ∀ d>0, ∃ t, |t| < d ∧ feasible h t ∧ imageEnergy s (sites h t) < imageEnergy s (sites h 0) := by
  intro d hd
  let v := min (d/2) (bound h)
  have hb : 0 < bound h := by unfold bound; linarith
  have hv : 0 < v := lt_min (by positivity) hb
  have hvb : v ≤ bound h := min_le_right _ _
  have hvd : v < d := (min_le_left _ _).trans_lt (by linarith)
  have hv' : v ≤ 1/2 := hvb.trans (by unfold bound; linarith)
  have hc : 0 < coord v := by
    simpa using strictMonoOn_coord (show (0:ℝ) ∈ Icc 0 (1/2) by constructor <;> norm_num)
      ⟨hv.le,hv'⟩ hv
  have hD := hasDerivWithinAt_phi (h := h) (Real.exp_pos _).le hQ
    (by constructor <;> norm_num : (0:ℝ) ∈ Icc 0 2)
  obtain ⟨y,hy,hyl⟩ := arbitrarily_small_decrease hD hneg hc
  have hmem : y ∈ Icc (coord 0) (coord v) := by simpa using Ioo_subset_Icc_self hy
  obtain ⟨t,ht,hty⟩ := intermediate_value_Icc hv.le continuous_coord.continuousOn hmem
  refine ⟨t, by simpa [abs_of_nonneg ht.1] using ht.2.trans_lt hvd,
    by simpa [feasible,abs_of_nonneg ht.1] using ht.2.trans hvb,?_⟩
  apply lt_of_not_ge
  intro H
  have hc' := (imageEnergy_le_iff hs h 0 t).mp H
  exact hyl.not_ge (by simpa [hty] using hc')


/-- At every floor up through the critical floor, equality on the packed face
occurs only at zero displacement. The four positive releases give strictness
in the whole simplex, including at the critical floor itself. -/
theorem centered_strict_through_critical {h : ℝ} (hh : 0 < h)
    (hcrit : h ≤ criticalFloor false (Real.exp (-(Real.pi^2)/8))) :
    ∃ r>0, ∀ t u, |t| < r → ‖u‖ < r →
      (∀ i, h ≤ Release.gaps (Release.sites h t u) i) → (t ≠ 0 ∨ u ≠ 0) →
      imageEnergy 8 (sites h 0) < imageEnergy 8 (Release.sites h t u) := by
  have h6 := hcrit.trans_lt (criticalFloor_spec false (Real.exp_pos _) nome_eight_le_faceQ).1.2
  apply strict_full_of_strict_face hh h6
  refine ⟨bound h, by unfold bound; linarith, ?_⟩
  intro t ht hne
  exact centered_strict_on_face (by norm_num) nome_eight_le_faceQ hh h6.le hcrit ht.le hne

/-- Beyond the critical floor, every neighborhood in the feasible simplex
contains an inward release of higher energy and a displacement of lower energy. -/
theorem centered_saddle_after_critical {h : ℝ}
    (hcrit : criticalFloor false (Real.exp (-(Real.pi^2)/8)) < h) (h6 : h < 1/6) :
    ∀ ε>0, ∃ t u, |t| < ε ∧ ‖u‖ < ε ∧
      (∀ i, h ≤ Release.gaps (Release.sites h t 0) i) ∧
      (∀ i, h ≤ Release.gaps (Release.sites h 0 u) i) ∧
      imageEnergy 8 (Release.sites h t 0) < imageEnergy 8 (sites h 0) ∧
      imageEnergy 8 (sites h 0) < imageEnergy 8 (Release.sites h 0 u) := by
  have hh : 0 < h := lt_trans (by norm_num : (0:ℝ)<1/8)
    ((criticalFloor_spec false (Real.exp_pos _) nome_eight_le_faceQ).1.1.trans hcrit)
  have neg := (centered_curvature_signs (s := 8) (by norm_num) nome_eight_le_faceQ hh h6.le).2.2 hcrit
  rw [centered_curvature (by norm_num) nome_eight_le_faceQ] at neg
  have hslope : phiD (Real.exp (-(Real.pi^2)/8)) h 0 < 0 :=
    by
      by_contra! H
      exact neg.not_ge (mul_nonneg (by positivity) H)
  exact full_saddle_of_face_descent hh h6
    (descent_of_negative_slope (by norm_num) nome_eight_le_faceQ hh h6 hslope)


private theorem widthEight_physicalEnergy (x : Fin 6 → ℝ) :
    physicalEnergy 8 1 x = imageEnergy 8 x := by
  simpa using physicalEnergy_eq_imageEnergy (N := 6) (by norm_num) 8 1
    (by norm_num) (by norm_num) x

/-- The same strict local minimum in the usual metric on six labelled
positions, after fixing translation by x₀=0. -/
theorem centered_strict_physical {h : ℝ} (hh : 0 < h)
    (hc : h ≤ criticalFloor false (Real.exp (-(Real.pi^2)/8))) :
    ∃ ε>0, ∀ x : Fin 6 → ℝ, dist x (sites h 0) < ε → x 0 = 0 →
      Feasible (by decide) h x → x ≠ sites h 0 → physicalEnergy 8 1 (sites h 0) < physicalEnergy 8 1 x := by
  simp_rw [widthEight_physicalEnergy]
  obtain ⟨r,hr,Hr⟩ := centered_strict_through_critical hh hc
  let T := fun x : Fin 6 → ℝ => x 3 - 1/2
  have hT : Continuous T := (continuous_apply 3).sub continuous_const
  have ht0 : T (sites h 0) = 0 := by simp [T,sites]
  have hU : Continuous (Release.releaseCoordinates h) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [Release.releaseCoordinates] <;> fun_prop
  have hu0 : Release.releaseCoordinates h (sites h 0) = 0 := by
    rw [← Release.zero_release_sites, Release.releaseCoordinates_sites]
  have hnear := (hT.abs.continuousAt (x := sites h 0)).tendsto.eventually_lt_const
    (by simpa [ht0] using hr : |T (sites h 0)| < r)
  have hsmall := (hU.norm.continuousAt (x := sites h 0)).tendsto.eventually_lt_const
    (by simpa [hu0] using hr : ‖Release.releaseCoordinates h (sites h 0)‖ < r)
  obtain ⟨ε,hε,Hε⟩ := Metric.eventually_nhds_iff.mp (hnear.and hsmall)
  refine ⟨ε,hε,?_⟩
  intro x hx hx0 hf hn
  let u := Release.releaseCoordinates h x
  have he : Release.sites h (T x) u = x := Release.reconstruct x hx0 h
  have hs : ∀ i, h ≤ Release.gaps (Release.sites h (T x) u) i := by
    simpa only [he,Release.gaps_eq_gap] using hf
  have hne : T x ≠ 0 ∨ u ≠ 0 := by
    by_contra! H
    apply hn
    simpa [H.1,H.2,Release.zero_release_sites] using he.symm
  simpa only [he] using Hr (T x) u (Hε hx).1 (Hε hx).2 hs hne

/-- Arbitrarily close feasible positions on both sides of the centered energy;
the five independent chart variables include all four releases. -/
theorem centered_saddle_physical {h : ℝ}
    (hc : criticalFloor false (Real.exp (-(Real.pi^2)/8)) < h) (h6 : h < 1/6) :
    ∀ ε>0, ∃ x y : Fin 6 → ℝ,
      dist x (sites h 0) < ε ∧ dist y (sites h 0) < ε ∧ x 0 = 0 ∧ y 0 = 0 ∧
      Feasible (by decide) h x ∧ Feasible (by decide) h y ∧
      physicalEnergy 8 1 x < physicalEnergy 8 1 (sites h 0) ∧
      physicalEnergy 8 1 (sites h 0) < physicalEnergy 8 1 y := by
  simp_rw [widthEight_physicalEnergy]
  intro ε hε
  let X := fun p : ℝ × (Fin 4 → ℝ) => Release.sites h p.1 p.2
  have hX : Continuous X := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [X,Release.sites] <;> fun_prop
  have hbase : X (0,0) = sites h 0 := Release.zero_release_sites h 0
  obtain ⟨δ,hδ,Hδ⟩ := Metric.continuousAt_iff.mp (hX.continuousAt (x := (0,0))) ε hε
  obtain ⟨t,u,ht,hu,hft,hfu,down,up⟩ := centered_saddle_after_critical hc h6 δ hδ
  refine ⟨X (t,0),X (0,u),?_,?_,rfl,rfl,?_,?_,down,up⟩
  · rw [← hbase]
    exact Hδ (by simpa [dist_prod_same_right, Real.dist_eq] using ht)
  · rw [← hbase]
    exact Hδ (by simpa [dist_prod_same_left] using hu)
  · simpa only [Feasible,Release.gaps_eq_gap,X] using hft
  · simpa only [Feasible,Release.gaps_eq_gap,X] using hfu

end GaussianChains.Bifurcation

