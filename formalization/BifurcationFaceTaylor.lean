import BifurcationAsymptotics
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FunProp

/-! Uniform Taylor expansion across the floor parameter for the physical
displacement. The parameter origin below represents the critical floor. -/

open Filter Asymptotics Set
open scoped Topology
noncomputable section
namespace GaussianChains.Bifurcation

/-- Derivatives along displacement while holding the floor fixed. -/
def displacementJet (f : ℝ × ℝ → ℝ) (n : ℕ) (u : ℝ × ℝ) : ℝ :=
  iteratedDeriv n (fun t => f (u.1,t)) u.2

theorem displacementJet_analytic (f : ℝ × ℝ → ℝ)
    (hf : ∀ u, AnalyticAt ℝ f u) (n : ℕ) (u : ℝ × ℝ) :
    AnalyticAt ℝ (displacementJet f n) u := by
  induction n generalizing u with
  | zero => simpa [displacementJet] using hf u
  | succ n ih =>
    have he : displacementJet f (n+1) =
        fun v => fderiv ℝ (displacementJet f n) v ((0,1) : ℝ × ℝ) := by
      funext v
      have hi : HasDerivAt (fun t : ℝ => (v.1,t)) (0,1) v.2 :=
        (hasDerivAt_const v.2 v.1).prodMk (hasDerivAt_id' v.2)
      have hd := (ih v).differentiableAt.hasFDerivAt.comp_hasDerivAt v.2 hi
      simpa only [displacementJet, iteratedDeriv_succ, Function.comp_def, Prod.mk.eta] using hd.deriv
    rw [he]
    exact ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : ℝ × ℝ)).analyticAt _).comp (ih u).fderiv

theorem odd_jet_zero (f : ℝ → ℝ) (heven : ∀ t, f (-t) = f t) {k : ℕ} (hk : Odd k) :
    iteratedDeriv k f 0 = 0 := by
  have h := iteratedDeriv_comp_neg k f 0
  rw [show (fun t => f (-t)) = f by funext t; exact heven t, hk.neg_one_pow] at h
  simp only [neg_zero, neg_smul, one_smul] at h
  linarith

private theorem taylor_positive (f : ℝ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hf : ∀ z, AnalyticAt ℝ f z) :
    ∃ r ∈ Ioo 0 t, f t -
      ∑ k ∈ Finset.range (n+1), (((k.factorial : ℝ)⁻¹*t^k) * iteratedDeriv k f 0) =
      iteratedDeriv (n+1) f r * t^(n+1) / (n+1).factorial := by
  have hs : ContDiff ℝ ((n:WithTop ℕ∞)+1) f := contDiff_iff_contDiffAt.mpr
    fun z => (hf z).contDiffAt
  obtain ⟨r,hr,H⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) ht (by
    exact_mod_cast hs.contDiffOn)
  refine ⟨r,hr,?_⟩
  rw [taylor_within_apply] at H
  simp only [sub_zero, smul_eq_mul] at H
  have hi (k : ℕ) : iteratedDerivWithin k f (Icc 0 t) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) (hf 0).contDiffAt ⟨le_rfl, ht.le⟩
  simpa only [hi] using H

/-- Simultaneous Taylor bounds for the energy and its force on the positive
half of an even displacement slice. A common sixth derivative controls both. -/
theorem even_energy_force_remainders (f : ℝ → ℝ) (hf : ∀ z, AnalyticAt ℝ f z)
    (heven : ∀ z, f (-z) = f z) {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (hbound : ∀ r ∈ Ioo 0 t, |iteratedDeriv 6 f r| ≤ C) :
    |f t - (f 0 + iteratedDeriv 2 f 0 * t^2/2 + iteratedDeriv 4 f 0 * t^4/24)| ≤ C*t^6 ∧
    |deriv f t - (iteratedDeriv 2 f 0*t + iteratedDeriv 4 f 0*t^3/6)| ≤ C*t^5 := by
  have h₁ := odd_jet_zero f heven (k := 1) (by decide)
  have h₃ := odd_jet_zero f heven (k := 3) (by decide)
  have h₅ := odd_jet_zero f heven (k := 5) (by decide)
  obtain ⟨r,hr,H⟩ := taylor_positive f 5 ht hf
  obtain ⟨r',hr',Hd⟩ := taylor_positive (deriv f) 4 ht (fun z => (hf z).deriv)
  simp only [← iteratedDeriv_succ'] at Hd
  norm_num [Finset.sum_range_succ, Nat.factorial, h₁, h₃, h₅] at H Hd
  constructor
  · have he : f t - (f 0 + iteratedDeriv 2 f 0*t^2/2 + iteratedDeriv 4 f 0*t^4/24) =
        iteratedDeriv 6 f r*t^6/720 := by linarith only [H]
    rw [he, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht.le 6)]
    have hb := mul_le_mul_of_nonneg_right (hbound r hr) (pow_nonneg ht.le 6)
    norm_num
    nlinarith [mul_nonneg hC (pow_nonneg ht.le 6)]
  · have he : deriv f t - (iteratedDeriv 2 f 0*t + iteratedDeriv 4 f 0*t^3/6) =
        iteratedDeriv 6 f r'*t^5/120 := by linarith only [Hd]
    rw [he, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht.le 5)]
    have hb := mul_le_mul_of_nonneg_right (hbound r' hr') (pow_nonneg ht.le 5)
    norm_num
    nlinarith [mul_nonneg hC (pow_nonneg ht.le 5)]

/-- Uniformity over a two-dimensional neighborhood follows from joint
regularity of the sixth displacement derivative. -/
theorem uniform_even_estimates (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t)) :
    ∃ C > (0:ℝ), ∃ r > (0:ℝ), ∀ δ t, |δ| < r → 0 < t → t < r →
      |f (δ,t) - (f (δ,0) + displacementJet f 2 (δ,0)*t^2/2 +
        displacementJet f 4 (δ,0)*t^4/24)| ≤ C*t^6 ∧
      |deriv (fun z => f (δ,z)) t - (displacementJet f 2 (δ,0)*t +
        displacementJet f 4 (δ,0)*t^3/6)| ≤ C*t^5 := by
  let C := |displacementJet f 6 0|+1
  have hC : 0 < C := by dsimp [C]; positivity
  have he := ((displacementJet_analytic f hf 6 0).continuousAt.abs.tendsto).eventually_lt_const
    (show |displacementJet f 6 0| < C by dsimp [C]; linarith)
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.1 he
  refine ⟨C,hC,r,hr,?_⟩
  intro δ t hδ ht htr
  refine even_energy_force_remainders (fun z => f (δ,z))
    (fun z => (hf (δ,z)).comp (analyticAt_const.prod analyticAt_id)) (heven δ) hC.le ht ?_
  intro z hz
  apply (H (y := (δ,z)) ?_).le
  simpa [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hz.1] using
    (max_lt hδ (hz.2.trans htr))

/-- The ordinary parameter Taylor remainder of an analytic coefficient, at
orders one and two. -/
theorem scalar_parameter_taylor (g : ℝ → ℝ) (hg : AnalyticAt ℝ g 0) :
    ((fun δ => g δ - g 0) =O[𝓝[>] 0] (fun δ : ℝ => δ)) ∧
    ((fun δ => g δ - (g 0 + deriv g 0*δ)) =O[𝓝[>] 0] (fun δ : ℝ => δ^2)) := by
  obtain ⟨p, hp⟩ := hg
  have h₀ : p.coeff 0 = g 0 := hp.coeff_zero _
  have h₁ : p.coeff 1 = deriv g 0 := hp.deriv.symm
  have H (n : ℕ) := (hp.isBigO_sub_partialSum_pow n).mono
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  constructor
  · refine (H 1).congr' ?_ ?_
    · filter_upwards with δ
      simp [FormalMultilinearSeries.partialSum, h₀]
    · filter_upwards [hpos] with δ hδ
      simp [Real.norm_eq_abs, abs_of_pos hδ]
  · refine (H 2).congr' ?_ ?_
    · filter_upwards with δ
      simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        h₀, h₁, pow_zero, one_mul, pow_one, smul_eq_mul, mul_comm δ]
    · filter_upwards with δ
      simp [Real.norm_eq_abs]

/-- Taylor control of the two centered coefficients as the floor varies. -/
theorem centered_coefficients_taylor (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    {A B : ℝ} (hcrit : displacementJet f 2 (0,0) = 0)
    (hAf : deriv (fun δ => displacementJet f 2 (δ,0)) 0 = A)
    (hBf : displacementJet f 4 (0,0) = B) :
    ((fun δ => displacementJet f 2 (δ,0) - A*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ^2)) ∧
    ((fun δ => displacementJet f 4 (δ,0) - B) =O[𝓝[>] 0] (fun δ : ℝ => δ)) := by
  have analytic (n : ℕ) : AnalyticAt ℝ (fun δ => displacementJet f n (δ,0)) 0 :=
    (displacementJet_analytic f hf n (0,0)).comp (f := fun δ : ℝ => (δ,(0:ℝ)))
      (show AnalyticAt ℝ (fun δ : ℝ => (δ,(0:ℝ))) 0 from analyticAt_id.prod analyticAt_const)
  exact ⟨by simpa only [hcrit,zero_add,hAf] using (scalar_parameter_taylor _ (analytic 2)).2,
    by simpa only [hBf] using (scalar_parameter_taylor _ (analytic 4)).1⟩

/-- On any small positive stationary branch, the Taylor expansion with the
*actual* derivatives in displacement and floor implies both laws (11). -/
theorem laws_of_even_stationary_branch (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t))
    (hcrit : displacementJet f 2 (0,0) = 0)
    {A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hAf : deriv (fun δ => displacementJet f 2 (δ,0)) 0 = A)
    (hBf : displacementJet f 4 (0,0) = B)
    (t : ℝ → ℝ) (ht : Tendsto t (𝓝[>] 0) (𝓝 0))
    (hstat : ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ deriv (fun u => f (δ,u)) (t δ) = 0) :
    ((fun δ => t δ - Real.sqrt (-6*A/B) * δ^(1/2:ℝ)) =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
    ((fun δ => (f (δ,0)-f (δ,t δ)) - (3*A^2/(2*B))*δ^2) =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) := by
  let κ := fun δ => displacementJet f 2 (δ,0)
  let β := fun δ => displacementJet f 4 (δ,0)
  obtain ⟨hkA,hbB⟩ := centered_coefficients_taylor f hf hcrit hAf hBf
  obtain ⟨C,hC,hC'⟩ := hkA.exists_pos
  obtain ⟨D,hD,hD'⟩ := hbB.exists_pos
  obtain ⟨M,hM,r,hr,hre⟩ := uniform_even_estimates f hf heven
  have hδlim : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hlocal : ∀ᶠ δ in 𝓝[>] 0,
      (0 < δ ∧ 0 < t δ) ∧ |κ δ-A*δ| ≤ C*δ^2 ∧ |β δ-B| ≤ D*δ ∧
      |f (δ,t δ) - (f (δ,0) + κ δ*t δ^2/2 + β δ*t δ^4/24)| ≤ M*t δ^6 ∧
      |κ δ + β δ/6*t δ^2| ≤ M*t δ^4 := by
    filter_upwards [hδpos, hδlim.eventually_lt_const hr, ht.eventually_lt_const hr,
      hstat, hC'.bound, hD'.bound] with δ hp hsmall htsmall hs hκ hβ
    obtain ⟨hE,hF⟩ := hre δ (t δ) (by rwa [abs_of_pos hp]) hs.1 htsmall
    refine ⟨⟨hp,hs.1⟩, by simpa only [Real.norm_eq_abs, abs_sq] using hκ,
      by simpa only [Real.norm_eq_abs, abs_of_pos hp] using hβ, hE, ?_⟩
    rw [hs.2, zero_sub, abs_neg] at hF
    apply le_of_mul_le_mul_right (a := t δ) _ hs.1
    calc
      |κ δ + β δ/6*t δ^2| * t δ = |κ δ*t δ + β δ*t δ^3/6| := by
        calc
          _ = |κ δ + β δ/6*t δ^2| * |t δ| := by rw [abs_of_pos hs.1]
          _ = _ := by rw [← abs_mul]; congr 1; ring
      _ ≤ M*t δ^5 := hF
      _ = _ := by ring
  have hz := squared_branch_of_stationarity t (A := A) hB ht (by
    refine isBigO_iff.2 ⟨C+D+M, ?_⟩
    filter_upwards [hlocal] with δ h
    obtain ⟨⟨hp,htp⟩, hκ,hβ,_,hf⟩ := h
    let Q := δ^2 + δ*t δ^2 + t δ^4
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    change |A*δ+B/6*t δ^2| ≤ (C+D+M)*|Q|
    rw [abs_of_nonneg hQ]
    have h₁ : δ^2 ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg hp.le (sq_nonneg (t δ)), sq_nonneg (t δ^2)]
    have h₂ : δ*t δ^2/6 ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg hp.le (sq_nonneg (t δ)), sq_nonneg δ, sq_nonneg (t δ^2)]
    have h₃ : t δ^4 ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg hp.le (sq_nonneg (t δ)), sq_nonneg δ]
    calc
      |A*δ + B/6*t δ^2| = |(κ δ+β δ/6*t δ^2) + (A*δ-κ δ) + (B-β δ)*(t δ^2/6)| :=
        congrArg abs (by ring)
      _ ≤ (|κ δ+β δ/6*t δ^2| + |A*δ-κ δ|) + |(B-β δ)*(t δ^2/6)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (M*t δ^4+C*δ^2) + (D*δ)*(t δ^2/6) := by
        rw [abs_sub_comm (A*δ), abs_mul, abs_sub_comm B,
          abs_of_nonneg (show 0 ≤ t δ^2/6 by positivity)]
        exact add_le_add (add_le_add hf hκ) (mul_le_mul_of_nonneg_right hβ (by positivity))
      _ ≤ (C+D+M)*Q := by nlinarith only [mul_le_mul_of_nonneg_left h₁ hC.le,
        mul_le_mul_of_nonneg_left h₂ hD.le, mul_le_mul_of_nonneg_left h₃ hM.le])
  have hK := div_pos (mul_pos_of_neg_of_neg (by norm_num : (-6:ℝ) < 0) hA) hB
  refine ⟨(reflected_displacements t hK (hstat.mono fun _ h => h.1.le) hz).1,
    energy_gain_of_quartic t (fun δ => f (δ,0)-f (δ,t δ)) hB hz ?_⟩
  obtain ⟨W, hW, hW'⟩ := hz.exists_pos
  let L := (-6*A/B)+W
  have hL : 0 < L := add_pos hK hW
  refine isBigO_iff.2 ⟨M*L^3 + C*L/2 + D*L^2/24, ?_⟩
  filter_upwards [hlocal, hW'.bound, hδlim.eventually_lt_const zero_lt_one] with δ h hZ hsmall
  obtain ⟨⟨hp,htp⟩,hκ,hβ,hE,_⟩ := h
  simp only [Real.norm_eq_abs, abs_sq] at hZ
  have hsq : t δ^2 ≤ L*δ := by
    have hδ' : δ^2 ≤ δ := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hsmall.le)]
    dsimp [L]
    nlinarith only [(le_abs_self _).trans hZ, mul_le_mul_of_nonneg_left hδ' hW.le]
  have h4 : t δ^4 ≤ L^2*δ^2 := by nlinarith only [pow_le_pow_left₀ (sq_nonneg _) hsq 2]
  have h6 : t δ^6 ≤ L^3*δ^3 := by nlinarith only [pow_le_pow_left₀ (sq_nonneg _) hsq 3]
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.le 3)]
  have hEr : |(f (δ,0)+κ δ*t δ^2/2+β δ*t δ^4/24)-f (δ,t δ)| ≤ M*t δ^6 := by
    rw [abs_sub_comm]
    exact hE
  calc
    _ = |(f (δ,0)+κ δ*t δ^2/2+β δ*t δ^4/24-f (δ,t δ)) +
          (A*δ-κ δ)*(t δ^2/2) + (B-β δ)*(t δ^4/24)| := congrArg abs (by ring)
    _ ≤ (|(f (δ,0)+κ δ*t δ^2/2+β δ*t δ^4/24)-f (δ,t δ)| +
          |(A*δ-κ δ)*(t δ^2/2)|) + |(B-β δ)*(t δ^4/24)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (M*t δ^6+(C*δ^2)*(t δ^2/2)) + (D*δ)*(t δ^4/24) := by
      simp only [abs_mul, abs_sub_comm (A*δ) (κ δ), abs_sub_comm B (β δ),
        abs_of_nonneg (show 0 ≤ t δ^2/2 by positivity), abs_of_nonneg (show 0 ≤ t δ^4/24 by positivity)]
      exact add_le_add (add_le_add hEr (mul_le_mul_of_nonneg_right hκ (by positivity)))
        (mul_le_mul_of_nonneg_right hβ (by positivity))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left h6 hM.le,
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le (sq_nonneg δ)),
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hD.le hp.le)]

end GaussianChains.Bifurcation
end
