import BifurcationFaceTaylor
import Mathlib.Analysis.Convex.Deriv

/-! Existence of a nonzero stationary branch, constructed from opposite
force signs on two square-root rays. -/

open Filter Asymptotics Set
open scoped Topology
noncomputable section
namespace GaussianChains.Bifurcation

private theorem ray_tendsto {c : ℝ} :
    Tendsto (fun δ : ℝ => Real.sqrt (c*δ)) (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  simpa using Real.continuous_sqrt.continuousAt.tendsto.comp (hi.const_mul c)

/-- Along an explicit square-root ray the normalized force has leading
coefficient `A + B c / 6`, with a uniform quadratic error before division by δ. -/
theorem force_on_ray (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t))
    (hcrit : displacementJet f 2 (0,0) = 0) {A B c : ℝ} (hc : 0 < c)
    (hAf : deriv (fun δ => displacementJet f 2 (δ,0)) 0 = A)
    (hBf : displacementJet f 4 (0,0) = B) :
    ∃ R > (0:ℝ), ∀ᶠ δ in 𝓝[>] 0,
      |deriv (fun z => f (δ,z)) (Real.sqrt (c*δ)) -
        (A+B*c/6)*δ*Real.sqrt (c*δ)| ≤ R*δ^2*Real.sqrt (c*δ) := by
  let κ := fun δ => displacementJet f 2 (δ,0)
  let β := fun δ => displacementJet f 4 (δ,0)
  obtain ⟨hkA,hbB⟩ := centered_coefficients_taylor f hf hcrit hAf hBf
  obtain ⟨C,hC,hC'⟩ := hkA.exists_pos
  obtain ⟨D,hD,hD'⟩ := hbB.exists_pos
  obtain ⟨M,hM,r,hr,hRe⟩ := uniform_even_estimates f hf heven
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨M*c^2+C+D*c/6, by positivity, ?_⟩
  filter_upwards [hp, hi.eventually_lt_const hr, (ray_tendsto (c := c)).eventually_lt_const hr,
    hC'.bound, hD'.bound] with δ hδ hd hray hh hb
  let v := Real.sqrt (c*δ)
  have hv : 0 < v := Real.sqrt_pos.2 (mul_pos hc hδ)
  have hv2 : v^2 = c*δ := Real.sq_sqrt (mul_nonneg hc.le hδ.le)
  have h3 : v^3 = c*δ*v := by calc
    _ = v^2*v := by ring
    _ = _ := by rw [hv2]
  have h5 : v^5 = c^2*δ^2*v := by calc
    _ = (v^2)^2*v := by ring
    _ = _ := by rw [hv2]; ring
  have hForce := (hRe δ v (by rwa [abs_of_pos hδ]) hv hray).2
  change |deriv (fun z => f (δ,z)) v - (κ δ*v + β δ*v^3/6)| ≤ M*v^5 at hForce
  simp only [Real.norm_eq_abs,abs_sq] at hh
  simp only [Real.norm_eq_abs,abs_of_pos hδ] at hb
  change |deriv (fun z => f (δ,z)) v - (A+B*c/6)*δ*v| ≤ _
  calc
    _ = |(deriv (fun z => f (δ,z)) v - (κ δ*v+β δ*v^3/6)) +
          (κ δ-A*δ)*v + (β δ-B)*(v^3/6)| := by congr 1; rw [h3]; ring
    _ ≤ (|deriv (fun z => f (δ,z)) v - (κ δ*v+β δ*v^3/6)| +
          |(κ δ-A*δ)*v|) + |(β δ-B)*(v^3/6)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (M*v^5+C*δ^2*v) + D*δ*(v^3/6) := by
      simp only [abs_mul,abs_of_pos hv,abs_of_nonneg (show 0 ≤ v^3/6 by positivity)]
      exact add_le_add (add_le_add hForce (mul_le_mul_of_nonneg_right hh hv.le))
        (mul_le_mul_of_nonneg_right hb (by positivity))
    _ = _ := by rw [h3,h5]; change _ = _*δ^2*v; ring

/-- Any nondegenerate even pitchfork has a positive stationary displacement
for every sufficiently small positive floor. The rays bracket the branch and
force its displacement to tend to zero. -/
theorem exists_even_stationary_branch (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t))
    (hcrit : displacementJet f 2 (0,0) = 0) {A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hAf : deriv (fun δ => displacementJet f 2 (δ,0)) 0 = A)
    (hBf : displacementJet f 4 (0,0) = B) :
    ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ deriv (fun z => f (δ,z)) (t δ) = 0 := by
  classical
  let lo := -3*A/B
  let hi := -12*A/B
  have hlo : 0 < lo := div_pos (mul_pos_of_neg_of_neg (by norm_num) hA) hB
  have hhi : 0 < hi := div_pos (mul_pos_of_neg_of_neg (by norm_num) hA) hB
  have hlt : lo < hi := (div_lt_div_iff_of_pos_right hB).2 (by linarith)
  have hl : A+B*lo/6 = A/2 := by dsimp [lo]; field_simp; ring
  have hh : A+B*hi/6 = -A := by dsimp [hi]; field_simp; ring
  obtain ⟨R,hR,HR⟩ := force_on_ray f hf heven hcrit hlo hAf hBf
  obtain ⟨S,hS,HS⟩ := force_on_ray f hf heven hcrit hhi hAf hBf
  have hi₀ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have small (r : ℝ) {e : ℝ} (he : 0 < e) : ∀ᶠ δ : ℝ in 𝓝[>] 0, r*δ < e :=
    (show Tendsto (fun δ : ℝ => r*δ) (𝓝[>] 0) (𝓝 0) by simpa using hi₀.const_mul r).eventually_lt_const he
  let P (δ : ℝ) := ∃ v ∈ Ioo (Real.sqrt (lo*δ)) (Real.sqrt (hi*δ)), deriv (fun z => f (δ,z)) v = 0
  have hP : ∀ᶠ δ : ℝ in 𝓝[>] 0, P δ := by
    filter_upwards [HR,HS, hδpos, small R (show 0 < -(A/2) by linarith),
      small S (show 0 < -A by linarith)] with δ hRδ hSδ hp hR' hS'
    let l := Real.sqrt (lo*δ)
    let u := Real.sqrt (hi*δ)
    let F := deriv (fun z => f (δ,z))
    have hlp : 0 < l := Real.sqrt_pos.2 (mul_pos hlo hp)
    have hup : 0 < u := Real.sqrt_pos.2 (mul_pos hhi hp)
    have hlu : l < u := Real.sqrt_lt_sqrt (mul_nonneg hlo.le hp.le) (mul_lt_mul_of_pos_right hlt hp)
    rw [hl] at hRδ
    rw [hh] at hSδ
    change |F l-A/2*δ*l| ≤ R*δ^2*l at hRδ
    change |F u- -A*δ*u| ≤ S*δ^2*u at hSδ
    have hfl : F l < 0 := by
      nlinarith only [(le_abs_self _).trans hRδ, mul_lt_mul_of_pos_right hR' (mul_pos hp hlp)]
    have hfu : 0 < F u := by
      nlinarith only [neg_abs_le (F u- -A*δ*u), hSδ, mul_lt_mul_of_pos_right hS' (mul_pos hp hup)]
    have hcon : Continuous F := continuous_iff_continuousAt.mpr fun z =>
      (((hf (δ,z)).comp (analyticAt_const.prod analyticAt_id)).deriv).continuousAt
    obtain ⟨v,hv,hzero⟩ := intermediate_value_Icc hlu.le hcon.continuousOn
      (show 0 ∈ Icc (F l) (F u) from ⟨hfl.le,hfu.le⟩)
    refine ⟨v,⟨lt_of_le_of_ne hv.1 ?_,lt_of_le_of_ne hv.2 ?_⟩,hzero⟩
    · intro h; exact hfl.ne ((congrArg F h).trans hzero)
    · intro h; exact hfu.ne' ((congrArg F h.symm).trans hzero)
  let t (δ : ℝ) := if h : P δ then h.choose else 0
  have hT : ∀ᶠ δ in 𝓝[>] 0, t δ ∈ Ioo (Real.sqrt (lo*δ)) (Real.sqrt (hi*δ)) ∧
      deriv (fun z => f (δ,z)) (t δ) = 0 := by
    filter_upwards [hP] with δ h
    simpa only [t,dif_pos h] using h.choose_spec
  have hTpos := hT.mono (fun δ h => (Real.sqrt_nonneg _).trans_lt h.1.1)
  exact ⟨t,squeeze_zero' (hTpos.mono fun _ h => h.le) (hT.mono fun _ h => h.1.2.le) ray_tendsto,
    hTpos.and (hT.mono fun _ h => h.2)⟩

/-- A positive fourth displacement derivative near the centered cell makes
its force strictly convex on a common positive half-interval in every nearby
floor slice. Evenness fixes the force and the third derivative at zero. -/
theorem nearby_force_strictConvex (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t))
    (hB : 0 < displacementJet f 4 (0,0)) :
    ∃ r > (0:ℝ), ∀ δ, |δ| < r → StrictConvexOn ℝ (Icc 0 r) (deriv (fun z => f (δ,z))) := by
  have hpre := ((displacementJet_analytic f hf 4 (0,0)).continuousAt.tendsto).eventually_const_lt hB
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.1 hpre
  refine ⟨r/2, by positivity, ?_⟩
  intro δ hd
  let g := fun z : ℝ => f (δ,z)
  have h3 (z : ℝ) : HasDerivAt (iteratedDeriv 3 g) (iteratedDeriv 4 g z) z := by
    have han := (displacementJet_analytic f hf 3 (δ,z)).comp
      (show AnalyticAt ℝ (fun y : ℝ => (δ,y)) z from analyticAt_const.prod analyticAt_id)
    have hh : AnalyticAt ℝ (iteratedDeriv 3 g) z := han
    exact (show iteratedDeriv 4 g z = deriv (iteratedDeriv 3 g) z from congrFun iteratedDeriv_succ _).symm ▸ hh.differentiableAt.hasDerivAt
  have hmono : StrictMonoOn (iteratedDeriv 3 g) (Icc 0 (r/2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun z _ => (h3 z).continuousAt.continuousWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    rw [(h3 z).deriv]
    apply H (y := (δ,z))
    simp only [Prod.mk_zero_zero, dist_zero_right, Prod.norm_def,Real.norm_eq_abs,abs_of_pos hz.1]
    exact max_lt (by linarith) (by linarith [hz.2])
  have h0 : iteratedDeriv 3 g 0 = 0 := odd_jet_zero g (heven δ) (by decide)
  have hcon : Continuous (deriv g) := continuous_iff_continuousAt.mpr fun z =>
    (((hf (δ,z)).comp (analyticAt_const.prod analyticAt_id)).deriv).continuousAt
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) hcon.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  have hpos := hmono (left_mem_Icc.mpr (by positivity)) ⟨hz.1.le,hz.2.le⟩ hz.1
  rw [h0] at hpos
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.iterate_succ_apply,
    Function.iterate_zero_apply] using hpos

/-- Each sufficiently near positive stationary displacement is unique at its
floor; strict convexity of the force rules out three collinear zeroes. -/
theorem nearby_stationary_unique (f : ℝ × ℝ → ℝ) (hf : ∀ u, AnalyticAt ℝ f u)
    (heven : ∀ h t, f (h,-t) = f (h,t)) (hB : 0 < displacementJet f 4 (0,0)) :
    ∃ r > (0:ℝ), ∀ δ, |δ| < r → ∀ t ∈ Ioc 0 r, ∀ u ∈ Ioc 0 r,
      deriv (fun z => f (δ,z)) t = 0 → deriv (fun z => f (δ,z)) u = 0 → t = u := by
  obtain ⟨r,hr,H⟩ := nearby_force_strictConvex f hf heven hB
  refine ⟨r,hr,?_⟩
  intro δ hd t ht u hu ht0 hu0
  let g := fun z => f (δ,z)
  have h0 : deriv g 0 = 0 := by simpa using odd_jet_zero g (heven δ) (k := 1) (by decide)
  have hn (a b : ℝ) (ha : 0 < a) (hb : b ≤ r) (hab : a < b)
      (h₁ : deriv g a = 0) (h₂ : deriv g b = 0) : False := by
    have h := (H δ hd).slope_strict_mono_adjacent (left_mem_Icc.mpr hr.le)
      ⟨(ha.trans hab).le,hb⟩ ha hab
    change (deriv g a - deriv g 0) / (a-0) < (deriv g b-deriv g a)/(b-a) at h
    simp [h0,h₁,h₂] at h
  rcases lt_trichotomy t u with h | h | h
  · exact (hn t u ht.1 hu.2 h ht0 hu0).elim
  · exact h
  · exact (hn u t hu.1 ht.2 h hu0 ht0).elim

end GaussianChains.Bifurcation
end
