import ClusterSeriesCandidate
import ClusterSeriesTrialMass
import ClusterSeriesCurvature

namespace GaussianChains.ClusterSeries

/-- A bound at the attained full-simplex minimum, using the admissible trial
above. It applies also before the exact ground-state classification is known. -/
theorem minimumEnergy_sub_dipole_le (k l : ℕ) {s h : ℝ} (hs : 0 < s)
    (h0 : 0 ≤ h) (h1 : h ≤ 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let N := (2*k+1)+(2*l+1)
    let q := Real.exp (-(Real.pi^2)/s)
    let η := 2*Real.pi*h
    minimumEnergy (by dsimp [N]; omega : 0 < N) h s - dipoleEnergy N s ≤
      (2*Real.sqrt (Real.pi/s)/(N:ℝ)) *
        ((2*(coeff k+coeff l)*η^2) * parityMoment Odd q 2) := by
  dsimp only
  let N : ℕ := (2*k+1)+(2*l+1)
  let q := Real.exp (-(Real.pi^2)/s)
  let η := 2*Real.pi*h
  let C := 2*Real.sqrt (Real.pi/s)/(N:ℝ)
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
    (neg_neg_of_pos (by positivity)) hs)
  have trial := minimumEnergy_le_packed k l hs h0 h1
  have hd : dipoleEnergy N s = 1-C*(4*parityMoment Odd q 0) := by
    rw [dipoleEnergy, kernel_dipole_difference hs]
    dsimp only [C, q]; ring
  change minimumEnergy _ h s - dipoleEnergy N s ≤ C * _
  calc
    _ ≤ (1 - C*packedMass k l q η) - dipoleEnergy N s := sub_le_sub_right trial _
    _ = C*(4*parityMoment Odd q 0 - packedMass k l q η) := by rw [hd]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (packedMass_trial_deficit_le k l (Real.exp_pos _) hq1 η) hc

/-- The published normalized bound F ≤ D(A+B)η² at the full minimum. -/
theorem minimum_normalized_deficit_le (k l : ℕ) {s h : ℝ} (hs : 0 < s)
    (h0 : 0 ≤ h) (h1 : h ≤ 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let N := (2*k+1)+(2*l+1)
    let q := Real.exp (-(Real.pi^2)/s)
    let c := Real.sqrt (Real.pi/s)
    let η := 2*Real.pi*h
    N*(minimumEnergy (by dsimp [N]; omega : 0 < N) h s - dipoleEnergy N s)/(2*c*q) ≤
      (angularCos 2 q 0 - angularCos 2 q Real.pi)*(coeff k+coeff l)*η^2 := by
  dsimp only
  let N := (2*k+1)+(2*l+1)
  let q := Real.exp (-(Real.pi^2)/s)
  let c := Real.sqrt (Real.pi/s)
  let η := 2*Real.pi*h
  have hn : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hq : 0 < q := Real.exp_pos _
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos Real.pi_pos hs)
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
    (neg_neg_of_pos (by positivity)) hs)
  let D := angularCos 2 q 0-angularCos 2 q Real.pi
  have hD : q*D = 2*parityMoment Odd q 2 := angularCos_oddMoment 2 hq hq1
  change (N:ℝ)*(minimumEnergy _ h s - dipoleEnergy N s)/(2*c*q) ≤ D*(coeff k+coeff l)*η^2
  apply (div_le_iff₀ (show 0 < 2*c*q by positivity)).2
  calc
    _ ≤ (N:ℝ) * ((2*c/(N:ℝ)) * ((2*(coeff k+coeff l)*η^2)*parityMoment Odd q 2)) :=
      mul_le_mul_of_nonneg_left (minimumEnergy_sub_dipole_le k l hs h0 h1) hn.le
    _ = (2*c)*((2*parityMoment Odd q 2)*(coeff k+coeff l)*η^2) := by
      field_simp [hn.ne']
    _ = _ := by rw [← hD]; ring

/-- For a balanced trial the curvature bound D < 4 supplies the uniform
2m²η² upper bound used by semicircle localization. -/
theorem minimum_balanced_deficit_le (k l : ℕ) (hk : k ≤ l+1) (hl : l ≤ k+1)
    {s h : ℝ} (hs : 0 < s) (hR : widthR (Real.exp (-(Real.pi^2)/s)) ≤ 2/3)
    (h0 : 0 ≤ h) (h1 : h ≤ 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let N := (2*k+1)+(2*l+1)
    let m : ℝ := (k:ℝ)+l+1
    let q := Real.exp (-(Real.pi^2)/s)
    let c := Real.sqrt (Real.pi/s)
    let η := 2*Real.pi*h
    N*(minimumEnergy (by dsimp [N]; omega : 0 < N) h s - dipoleEnergy N s)/(2*c*q) ≤
      2*m^2*η^2 := by
  have hq := Real.exp_pos (-(Real.pi^2)/s)
  have hq1 : Real.exp (-(Real.pi^2)/s) < 1 := Real.exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hs)
  have hh := (locking_D_bounds hq.le hq1 hR).2.le
  have hA : 0 ≤ coeff k + coeff l := by dsimp [coeff]; positivity
  have hab : 2*(coeff k+coeff l) ≤ ((k:ℝ)+l+1)^2 := by
    rcases (show k=l ∨ k=l+1 ∨ l=k+1 by omega) with h' | h' | h'
    all_goals subst_vars; simp [coeff]; ring_nf; norm_num
  dsimp only
  refine (minimum_normalized_deficit_le k l hs h0 h1).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right hh hA).trans (by linarith only [hab])

/-- Trial bound at arbitrary positive even particle count. The balanced split
is constructed from m, not imposed on the minimizing configuration. -/
theorem minimum_deficit_le (m : ℕ) (hm : 0 < m) {s h : ℝ} (hs : 0 < s)
    (hR : widthR (Real.exp (-(Real.pi^2)/s)) ≤ 2/3)
    (h0 : 0 ≤ h) (h1 : h ≤ 1 / ((2*m:ℕ):ℝ)) :
    let N := 2*m
    let q := Real.exp (-(Real.pi^2)/s)
    let c := Real.sqrt (Real.pi/s)
    let η := 2*Real.pi*h
    N*(minimumEnergy (by dsimp [N]; omega : 0 < N) h s - dipoleEnergy N s)/(2*c*q) ≤
      2*(m:ℝ)^2*η^2 := by
  let k := (m-1)/2
  let l := m-1-k
  have hk : k ≤ l+1 := by dsimp [l,k]; omega
  have hl : l ≤ k+1 := by dsimp [l,k]; omega
  have hn : (2*k+1)+(2*l+1) = 2*m := by dsimp [l,k]; omega
  have hm' : k+l+1 = m := by dsimp [l,k]; omega
  have hh := minimum_balanced_deficit_le k l hk hl hs hR h0 (by rwa [hn])
  dsimp only at hh ⊢
  have hcast : (k:ℝ)+(l:ℝ)+1 = (m:ℝ) := by exact_mod_cast hm'
  simpa only [hn, hcast] using hh

end GaussianChains.ClusterSeries

