import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Remainder estimates for the even pitchfork in equation (11). The right-hand
filter uses the floor increment `δ = h - h_c`. These lemmas perform the
substitution into the stationary equation and energy after Taylor expansion. -/

open Filter Asymptotics
open scoped Topology

namespace GaussianChains.Bifurcation

private theorem eventually_floor_pos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ :=
  self_mem_nhdsWithin

private theorem eventually_floor_lt_one : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
  nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)

/-- Taking a square root loses exactly one half-power of the floor increment.
The absolute value describes both reflected branches without choosing a sign. -/
theorem displacement_of_squared_branch (t : ℝ → ℝ) {K : ℝ} (hK : 0 < K)
    (hz : (fun δ => t δ ^ 2 - K * δ) =O[𝓝[>] 0] (fun δ : ℝ => δ ^ 2)) :
    (fun δ => |t δ| - Real.sqrt K * Real.sqrt δ)
      =O[𝓝[>] 0] (fun δ : ℝ => δ * Real.sqrt δ) := by
  obtain ⟨C, hC⟩ := isBigO_iff.1 hz
  refine isBigO_iff.2 ⟨C / Real.sqrt K, ?_⟩
  filter_upwards [hC, eventually_floor_pos] with δ hδ hpos
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)] at hδ
  let r := Real.sqrt K * Real.sqrt δ
  have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hK) (Real.sqrt_pos.2 hpos)
  have hr2 : r ^ 2 = K * δ := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hpos.le]
  have hbound : abs (|t δ| - r) * r ≤ C * δ ^ 2 := calc
    abs (|t δ| - r) * r ≤ abs (|t δ| - r) * (|t δ| + r) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _)
    _ = |t δ ^ 2 - K * δ| := by
      rw [← abs_of_nonneg (show 0 ≤ |t δ| + r from add_nonneg (abs_nonneg _) hr.le),
        ← abs_mul, mul_comm (|t δ| - r), ← sq_sub_sq, sq_abs, hr2]
    _ ≤ _ := hδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (Real.sqrt_nonneg _))]
  change abs (|t δ| - r) ≤ _
  apply le_of_mul_le_mul_right (a := r) _ hr
  calc
    abs (|t δ| - r) * r ≤ C * δ ^ 2 := hbound
    _ = C * δ * Real.sqrt δ ^ 2 := by rw [Real.sq_sqrt hpos.le]; ring
    _ = C / Real.sqrt K * (δ * Real.sqrt δ) * r := by
      dsimp [r]
      field_simp [(Real.sqrt_pos.2 hK).ne']

/-- A positive representative and its reflected partner in the exponent
notation of equation (11). -/
theorem reflected_displacements (t : ℝ → ℝ) {K : ℝ} (hK : 0 < K)
    (ht : ∀ᶠ δ in 𝓝[>] 0, 0 ≤ t δ)
    (hz : (fun δ => t δ ^ 2 - K*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ^2)) :
    ((fun δ => t δ - Real.sqrt K * δ^(1/2 : ℝ))
      =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2 : ℝ))) ∧
    ((fun δ => -t δ - (-Real.sqrt K) * δ^(1/2 : ℝ))
      =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2 : ℝ))) := by
  have h := displacement_of_squared_branch t hK hz
  have hp : (fun δ => t δ - Real.sqrt K * δ^(1/2 : ℝ))
      =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2 : ℝ)) := by
    refine h.congr' ?_ ?_
    · filter_upwards [ht] with δ ht
      rw [abs_of_nonneg ht, Real.sqrt_eq_rpow δ]
    · filter_upwards [eventually_floor_pos] with δ hδ
      rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hδ, Real.rpow_one, Real.sqrt_eq_rpow]
  refine ⟨hp, hp.neg_left.congr_left ?_⟩
  intro δ
  dsimp
  ring

/-- After completing the square, substituting the squared branch into the
quartic energy retains a cubic remainder, with the coefficient from (11). -/
theorem energy_gain_of_quartic (t gain : ℝ → ℝ) {A B : ℝ} (hB : 0 < B)
    (hz : (fun δ => t δ ^ 2 - (-6*A/B)*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ ^ 2))
    (hE : (fun δ => gain δ + A/2*δ*t δ ^ 2 + B/24*t δ ^ 4)
      =O[𝓝[>] 0] (fun δ : ℝ => δ ^ 3)) :
    (fun δ => gain δ - (3*A^2/(2*B))*δ^2)
      =O[𝓝[>] 0] (fun δ : ℝ => δ ^ 3) := by
  obtain ⟨C, hC⟩ := isBigO_iff.1 hz
  obtain ⟨D, hD⟩ := isBigO_iff.1 hE
  refine isBigO_iff.2 ⟨D + (B/24)*C^2, ?_⟩
  filter_upwards [hC, hD, eventually_floor_pos, eventually_floor_lt_one] with δ hz hE hδ hsmall
  let e := t δ ^ 2 - (-6*A/B)*δ
  have he : |e| ≤ C * δ^2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)] using hz
  have he2 : e ^ 2 ≤ C ^ 2 * δ ^ 3 := calc
    e ^ 2 = |e| ^ 2 := (sq_abs _).symm
    _ ≤ (C * δ^2)^2 := pow_le_pow_left₀ (abs_nonneg _) he 2
    _ = C^2 * δ^3 * δ := by ring
    _ ≤ C^2 * δ^3 * 1 := mul_le_mul_of_nonneg_left hsmall.le (by positivity)
    _ = _ := mul_one _
  have heq : gain δ - (3*A^2/(2*B))*δ^2 =
      (gain δ + A/2*δ*t δ^2 + B/24*t δ^4) - B/24*e^2 := by
    dsimp [e]
    field_simp
    ring
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hδ3] at hE ⊢
  rw [heq]
  calc
    _ ≤ |gain δ + A/2*δ*t δ^2 + B/24*t δ^4| + |B/24*e^2| := abs_sub _ _
    _ = |gain δ + A/2*δ*t δ^2 + B/24*t δ^4| + B/24*e^2 := by
      rw [abs_of_nonneg (show 0 ≤ B/24*e^2 by positivity)]
    _ ≤ D*δ^3 + B/24*(C^2*δ^3) := add_le_add hE (mul_le_mul_of_nonneg_left he2 (by positivity))
    _ = _ := by ring

/-- On any nonzero stationary branch tending to the centered cell, the
Taylor remainder in the divided stationary equation first forces `t² = O(δ)`,
then fixes the linear coefficient of `t²`. -/
theorem squared_branch_of_stationarity (t : ℝ → ℝ) {A B : ℝ} (hB : 0 < B)
    (ht : Tendsto t (𝓝[>] 0) (𝓝 0))
    (hstationary : (fun δ => A*δ + B/6*t δ^2)
      =O[𝓝[>] 0] (fun δ : ℝ => δ^2 + δ*t δ^2 + t δ^4)) :
    (fun δ => t δ^2 - (-6*A/B)*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ^2) := by
  obtain ⟨C, hCpos, hC⟩ := hstationary.exists_pos
  let M := (C + |A|) / (B/12)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hz : Tendsto (fun δ => t δ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.pow 2
  have hfloor : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hε : Tendsto (fun δ => C * (δ + t δ^2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hfloor.add hz).const_mul C
  have hsmall := hε.eventually_lt_const (show 0 < B/12 by positivity)
  refine isBigO_iff.2 ⟨(6/B) * (C*(1+M+M^2)), ?_⟩
  filter_upwards [hC.bound, hsmall, eventually_floor_pos, eventually_floor_lt_one]
    with δ hstat hsmall hδ hδsmall
  have hnonneg : 0 ≤ δ^2 + δ*t δ^2 + t δ^4 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hstat
  have hu : t δ ^ 2 ≤ M * δ := by
    have hα := (le_abs_self (A*δ + B/6*t δ^2)).trans hstat
    have hsmall' := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg (t δ))
    have hδ' := mul_le_mul_of_nonneg_left
      (show δ ^ 2 ≤ δ by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδsmall.le)])
      hCpos.le
    have h := mul_le_mul_of_nonneg_right (neg_abs_le A) hδ.le
    have hβ : t δ^2 * (B/12) ≤ (C+|A|)*δ := by nlinarith only [hα, hsmall', hδ', h]
    apply le_of_mul_le_mul_right (a := B/12) _ (by positivity)
    calc
      t δ^2 * (B/12) ≤ (C+|A|)*δ := hβ
      _ = M*δ*(B/12) := by dsimp [M]; field_simp
  have hbound : δ^2 + δ*t δ^2 + t δ^4 ≤ (1+M+M^2)*δ^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hu hδ.le
    have h₂ := pow_le_pow_left₀ (sq_nonneg (t δ)) hu 2
    nlinarith only [h₁, h₂]
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)]
  have heq : t δ^2 - (-6*A/B)*δ = (6/B) * (A*δ + B/6*t δ^2) := by
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos (show 0 < 6/B by positivity)]
  calc
    _ ≤ (6/B) * (C * ((1+M+M^2)*δ^2)) :=
      mul_le_mul_of_nonneg_left
        (hstat.trans (mul_le_mul_of_nonneg_left hbound hCpos.le)) (by positivity)
    _ = _ := by ring

private theorem squared_coordinates_tendsto (t : ℝ → ℝ) (ht : Tendsto t (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ : ℝ => (δ, t δ^2)) (𝓝[>] 0) (𝓝 0) := by
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hz : Tendsto (fun δ => t δ^2) (𝓝[>] 0) (𝓝 0) := by simpa using ht.pow 2
  exact hδ.prodMk_nhds hz

/-- For analytic germs in the squared coordinate, only the displayed Taylor
jets and the stationary equation on the branch are needed to obtain both
orders in (11). `F` is the divided stationary equation, and `G` is the
centered-minus-displaced energy. -/
theorem analytic_branch_expansions
    (F G : ℝ × ℝ → ℝ) (p q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) (hG : HasFPowerSeriesAt G q 0)
    {A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hlin : ∀ u : ℝ × ℝ, p.partialSum 2 u = A*u.1 + B/6*u.2)
    (hquad : ∀ u : ℝ × ℝ, q.partialSum 3 u = -(A/2*u.1*u.2 + B/24*u.2^2))
    (t : ℝ → ℝ) (ht : Tendsto t (𝓝[>] 0) (𝓝 0))
    (hroot : ∀ᶠ δ in 𝓝[>] 0, F (δ,t δ^2) = 0) :
    ((fun δ => |t δ| - Real.sqrt (-6*A/B) * Real.sqrt δ)
      =O[𝓝[>] 0] (fun δ : ℝ => δ * Real.sqrt δ)) ∧
    ((fun δ => G (δ,t δ^2) - (3*A^2/(2*B))*δ^2)
      =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) := by
  have hu := squared_coordinates_tendsto t ht
  obtain ⟨C, hc, herr⟩ := ((hF.isBigO_sub_partialSum_pow 2).comp_tendsto hu).exists_pos
  have hz := squared_branch_of_stationarity t (A := A) hB ht (by
    refine isBigO_iff.2 ⟨C, ?_⟩
    filter_upwards [herr.bound, hroot, eventually_floor_pos] with δ h hr hδ
    have hnon : 0 ≤ δ^2 + δ*t δ^2 + t δ^4 := by positivity
    simp only [Function.comp_apply, zero_add, hlin, hr, zero_sub, norm_neg,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(δ,t δ^2)‖)] at h
    simp only [Real.norm_eq_abs, abs_of_nonneg hnon]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ.le, abs_of_nonneg (sq_nonneg (t δ))]
    rcases le_total δ (t δ^2) with hle | hle
    · rw [max_eq_right hle]
      nlinarith [mul_nonneg hδ.le (sq_nonneg (t δ)), sq_nonneg δ]
    · rw [max_eq_left hle]
      nlinarith [mul_nonneg hδ.le (sq_nonneg (t δ)), sq_nonneg (t δ^2)])
  have hk : 0 < -6*A/B := div_pos (mul_pos_of_neg_of_neg (by norm_num) hA) hB
  refine ⟨displacement_of_squared_branch t hk hz, energy_gain_of_quartic t _ hB hz ?_⟩
  obtain ⟨D, hd, htail⟩ := ((hG.isBigO_sub_partialSum_pow 3).comp_tendsto hu).exists_pos
  obtain ⟨C', hc', hz'⟩ := hz.exists_pos
  let M := max 1 ((-6*A/B)+C')
  refine isBigO_iff.2 ⟨D*M^3, ?_⟩
  filter_upwards [htail.bound, hz'.bound, eventually_floor_pos, eventually_floor_lt_one]
    with δ hG hZ hδ hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)] at hZ
  have hZ' := (le_abs_self _).trans hZ
  have hδle : δ^2 ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hsmall.le)]
  have hm : ‖(δ, t δ^2)‖ ≤ M*δ := by
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ.le, abs_of_nonneg (sq_nonneg (t δ))]
    refine max_le ?_ ?_
    · simpa only [one_mul, M] using mul_le_mul_of_nonneg_right (le_max_left 1 ((-6*A/B)+C')) hδ.le
    · apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right 1 ((-6*A/B)+C')) hδ.le)
      nlinarith only [hZ', mul_le_mul_of_nonneg_left hδle hc'.le]
  simp only [Function.comp_apply, zero_add, hquad, sub_neg_eq_add] at hG
  have herr' : |G (δ,t δ^2) + A/2*δ*t δ^2 + B/24*t δ^4| ≤ D*‖(δ,t δ^2)‖^3 := by
    rw [← add_assoc, ← pow_mul] at hG
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)] using hG
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hδ.le 3)]
  calc
    _ ≤ D*‖(δ,t δ^2)‖^3 := herr'
    _ ≤ D*(M*δ)^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hm 3) hd.le
    _ = _ := by ring

/-- The positive derivative in the squared coordinate makes the divided
stationary equation strictly increasing in each sufficiently short nearby
fiber. Thus it can have at most one nearby squared displacement at fixed floor. -/
theorem nearby_fiber_strict
    (F : ℝ × ℝ → ℝ) (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) {b : ℝ} (hb : 0 < b)
    (hjet : ∀ z : ℝ, p 1 (fun _ => (0,z)) = b*z) :
    ∀ᶠ w : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 0,
      w.1.1 = w.2.1 → w.1.2 < w.2.2 → F w.1 < F w.2 := by
  obtain ⟨C, hc, htail⟩ := hF.isBigO_image_sub_norm_mul_norm_sub.exists_pos
  have hnear : Tendsto (fun w : (ℝ × ℝ) × (ℝ × ℝ) => C*‖w‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.continuousAt (x := (0 : (ℝ × ℝ) × (ℝ × ℝ)))).tendsto.const_mul C
  filter_upwards [htail.bound, hnear.eventually_lt_const hb] with w h hclose
  intro hδ hz
  have hdiff : w.1 - w.2 = (0, w.1.2 - w.2.2) := by ext <;> simp [hδ]
  have hn : ‖w.1 - w.2‖ = w.2.2 - w.1.2 := by
    rw [hdiff, Prod.norm_def]
    simp [Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hz), sub_nonneg.mpr hz.le]
  change ‖F w.1 - F w.2 - p 1 (fun _ => w.1 - w.2)‖ ≤
    C * ‖‖w - 0‖ * ‖w.1 - w.2‖‖ at h
  rw [sub_zero, hn, hdiff, hjet, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hz.le))] at h
  have hu := (le_abs_self _).trans h
  have hlt := mul_lt_mul_of_pos_right hclose (sub_pos.mpr hz)
  nlinarith only [hu, hlt]

/-- The divided equation changes sign between the rays `z=0` and
`z=(-2A/b)δ`. It therefore has a strictly positive root between these rays
for every sufficiently small positive floor increment. -/
theorem positive_stationary_root
    (F : ℝ × ℝ → ℝ) (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) {A b : ℝ} (hA : A < 0) (hb : 0 < b)
    (hlin : ∀ u : ℝ × ℝ, p.partialSum 2 u = A*u.1 + b*u.2) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ z ∈ Set.Ioo 0 ((-2*A/b)*δ), F (δ,z) = 0 := by
  let k := -2*A/b
  have hk : 0 < k := div_pos (mul_pos_of_neg_of_neg (by norm_num) hA) hb
  have hkval : A + b*k = -A := by dsimp [k]; field_simp; ring
  have hδlim : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have small_mul (d : ℝ) {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ δ : ℝ in 𝓝[>] 0, d*δ < ε := by
    exact (show Tendsto (fun δ : ℝ => d*δ) (𝓝[>] 0) (𝓝 0) by
      simpa using hδlim.const_mul d).eventually_lt_const hε
  obtain ⟨C, hc, htail⟩ := (hF.isBigO_sub_partialSum_pow 2).exists_pos
  have norm_bound {δ z l : ℝ} (hδ : 0 ≤ δ) (hz : 0 ≤ z) (hl : 0 ≤ l) (hz' : z ≤ l*δ) :
      ‖(δ,z)‖ ≤ (1+l)*δ := by
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ, abs_of_nonneg hz]
    apply max_le
    · nlinarith [mul_nonneg hl hδ]
    · linarith
  have ray (l : ℝ) (hl : 0 ≤ l) : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      |F (δ,l*δ) - (A+b*l)*δ| ≤ C*(1+l)^2*δ^2 := by
    have hlim : Tendsto (fun δ : ℝ => (δ,l*δ)) (𝓝[>] 0) (𝓝 0) :=
      hδlim.prodMk_nhds (by simpa using hδlim.const_mul l)
    filter_upwards [hlim.eventually htail.bound, eventually_floor_pos] with δ h hδ
    simp only [zero_add, hlin, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(δ,l*δ)‖)] at h
    calc
      _ = |F (δ,l*δ) - (A*δ+b*(l*δ))| := by ring_nf
      _ ≤ _ := h
      _ ≤ C*((1+l)*δ)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (norm_nonneg _) (norm_bound hδ.le (mul_nonneg hl hδ.le) hl le_rfl) 2) hc.le
      _ = _ := by ring
  obtain ⟨r, hr, hrF⟩ := Metric.eventually_nhds_iff.1 hF.analyticAt.eventually_continuousAt
  filter_upwards [ray 0 le_rfl, ray k hk.le, small_mul C (neg_pos.mpr hA),
    small_mul (C*(1+k)^2) (neg_pos.mpr hA), small_mul (1+k) hr, eventually_floor_pos]
    with δ hzero hfar hsmall₀ hsmall₁ hnear hδ
  simp only [zero_mul, mul_zero, add_zero, one_pow, mul_one] at hzero
  rw [hkval] at hfar
  have hneg : F (δ,0) < 0 := by
    have h := (le_abs_self _).trans hzero
    nlinarith only [h, mul_lt_mul_of_pos_right hsmall₀ hδ]
  have hpos : 0 < F (δ,k*δ) := by
    have h := neg_abs_le (F (δ,k*δ) - -A*δ)
    nlinarith only [h, hfar, mul_lt_mul_of_pos_right hsmall₁ hδ]
  have hcont : ContinuousOn (fun z : ℝ => F (δ,z)) (Set.Icc 0 (k*δ)) := by
    intro z hz
    have hdist : dist (δ,z) (0 : ℝ × ℝ) < r := by
      rw [dist_zero_right]
      exact (norm_bound hδ.le hz.1 hk.le hz.2).trans_lt hnear
    exact ((hrF hdist).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzero_image := intermediate_value_Icc (mul_pos hk hδ).le hcont
    (show 0 ∈ Set.Icc (F (δ,0)) (F (δ,k*δ)) from ⟨hneg.le, hpos.le⟩)
  obtain ⟨z, hz, hroot⟩ := hzero_image
  refine ⟨z, ⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩, hroot⟩
  · rintro rfl
    exact hneg.ne hroot
  · rintro rfl
    exact hpos.ne' hroot

/-- Recover the squared displacement directly from the packed-face
coordinate `y = 1 - cos (ωt)`. Its leading coefficient is scaled by
`2/ω²`; this lemma avoids taking an inverse cosine at its singular endpoint. -/
theorem squared_branch_of_face_coord (t : ℝ → ℝ) {ω K : ℝ} (hω : 0 < ω)
    (ht : Tendsto t (𝓝[>] 0) (𝓝 0))
    (hy : (fun δ => 1 - Real.cos (ω*t δ) - K*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ^2)) :
    (fun δ => t δ^2 - (2*K/ω^2)*δ) =O[𝓝[>] 0] (fun δ : ℝ => δ^2) := by
  have hs := squared_branch_of_stationarity t (A := -K) (B := 3*ω^2) (by positivity) ht (by
    obtain ⟨C, hc, hc'⟩ := hy.exists_pos
    let D := ω^4*(5/96)
    have hd : 0 ≤ D := by dsimp [D]; positivity
    have hsmall : ∀ᶠ δ in 𝓝[>] 0, |ω*t δ| < 1 :=
      (show Tendsto (fun δ => |ω*t δ|) (𝓝[>] 0) (𝓝 0) by
        simpa using (ht.const_mul ω).abs).eventually_lt_const zero_lt_one
    refine isBigO_iff.2 ⟨C+D, ?_⟩
    filter_upwards [eventually_floor_pos, hsmall, hc'.bound] with δ hδ hsmall h
    have hnon : 0 ≤ δ^2 + δ*t δ^2 + t δ^4 := by positivity
    simp only [Real.norm_eq_abs, abs_sq] at h
    simp only [Real.norm_eq_abs, abs_of_nonneg hnon]
    have hcos := Real.cos_bound hsmall.le
    rw [show |ω*t δ|^4 = (ω*t δ)^4 by rw [← abs_pow, abs_of_nonneg (by positivity)]] at hcos
    have hcross := mul_nonneg hδ.le (sq_nonneg (t δ))
    have h₁ : δ^2 ≤ δ^2 + δ*t δ^2 + t δ^4 := by nlinarith [sq_nonneg (t δ^2)]
    have h₂ : t δ^4 ≤ δ^2 + δ*t δ^2 + t δ^4 := by nlinarith [sq_nonneg δ]
    calc
      _ = |(1 - Real.cos (ω*t δ) - K*δ) + (Real.cos (ω*t δ) - (1-(ω*t δ)^2/2))| :=
        congrArg abs (by ring)
      _ ≤ _ := abs_add_le _ _
      _ ≤ C*δ^2 + D*t δ^4 := add_le_add h (hcos.trans_eq (by dsimp [D]; ring))
      _ ≤ C*(δ^2 + δ*t δ^2 + t δ^4) + D*(δ^2 + δ*t δ^2 + t δ^4) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ hc.le) (mul_le_mul_of_nonneg_left h₂ hd)
      _ = _ := by ring)
  have heq : -6*(-K)/(3*ω^2) = 2*K/ω^2 := by field_simp; ring
  rwa [heq] at hs

/-- Choose the bifurcating positive displacement on every sufficiently small
positive floor. Its reflected partner has the same squared coordinate and gain.
This statement constructs the branch from the two analytic jets. -/
theorem exists_pitchfork_branch
    (F G : ℝ × ℝ → ℝ) (p q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) (hG : HasFPowerSeriesAt G q 0)
    {A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hlin : ∀ u : ℝ × ℝ, p.partialSum 2 u = A*u.1 + B/6*u.2)
    (hquad : ∀ u : ℝ × ℝ, q.partialSum 3 u = -(A/2*u.1*u.2 + B/24*u.2^2)) :
    ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
      (∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ F (δ,t δ^2) = 0) ∧
      ((fun δ => t δ - Real.sqrt (-6*A/B) * Real.sqrt δ)
        =O[𝓝[>] 0] (fun δ : ℝ => δ * Real.sqrt δ)) ∧
      ((fun δ => G (δ,t δ^2) - (3*A^2/(2*B))*δ^2)
        =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) := by
  classical
  let K := -2*A/(B/6)
  let S (δ : ℝ) := ∃ z ∈ Set.Ioo 0 (K*δ), F (δ,z) = 0
  have hS : ∀ᶠ δ : ℝ in 𝓝[>] 0, S δ :=
    positive_stationary_root F p hF hA (by positivity : 0 < B/6) hlin
  let z (δ : ℝ) := if h : S δ then h.choose else 0
  have hz : ∀ᶠ δ in 𝓝[>] 0, z δ ∈ Set.Ioo 0 (K*δ) ∧ F (δ,z δ) = 0 := by
    filter_upwards [hS] with δ h
    simpa only [z, dif_pos h] using h.choose_spec
  have hδlim : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hzlim : Tendsto z (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (hz.mono fun _ h => h.1.1.le) (hz.mono fun _ h => h.1.2.le)
      (by simpa using hδlim.const_mul K)
  let t := fun δ => Real.sqrt (z δ)
  have ht : Tendsto t (𝓝[>] 0) (𝓝 0) := by
    simpa [t] using Real.continuous_sqrt.continuousAt.tendsto.comp hzlim
  have hroot : ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ F (δ,t δ^2) = 0 := by
    filter_upwards [hz] with δ h
    exact ⟨Real.sqrt_pos.2 h.1.1, by simpa only [t, Real.sq_sqrt h.1.1.le] using h.2⟩
  obtain ⟨hdisp,hgain⟩ := analytic_branch_expansions F G p q hF hG hA hB hlin hquad
    t ht (hroot.mono fun _ h => h.2)
  exact ⟨t, ht, hroot, hdisp.congr_left (fun δ => by change |Real.sqrt (z δ)| - _ = _; rw [abs_of_nonneg (Real.sqrt_nonneg _)]), hgain⟩

/-- Among sufficiently near points at the same floor, equal values of the
divided stationary equation have the same squared displacement. -/
theorem nearby_fiber_injective
    (F : ℝ × ℝ → ℝ) (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) {b : ℝ} (hb : 0 < b)
    (hjet : ∀ z : ℝ, p 1 (fun _ => (0,z)) = b*z) :
    ∀ᶠ w : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 0,
      w.1.1 = w.2.1 → F w.1 = F w.2 → w.1.2 = w.2.2 := by
  have h := nearby_fiber_strict F p hF hb hjet
  have hs : Tendsto Prod.swap (𝓝 (0 : (ℝ × ℝ) × (ℝ × ℝ))) (𝓝 0) :=
    continuous_swap.continuousAt
  filter_upwards [h, hs.eventually h] with w h₁ h₂
  intro hfirst heq
  rcases lt_trichotomy w.1.2 w.2.2 with hlt | he | hgt
  · exact False.elim ((h₁ hfirst hlt).ne heq)
  · exact he
  · exact False.elim ((h₂ hfirst.symm hgt).ne heq.symm)

/-- The first jet used for the branch expansion also supplies the vertical
derivative required for uniqueness. -/
theorem divided_equation_unique_near_zero
    (F : ℝ × ℝ → ℝ) (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hF : HasFPowerSeriesAt F p 0) {A b : ℝ} (hb : 0 < b)
    (hlin : ∀ u : ℝ × ℝ, p.partialSum 2 u = A*u.1 + b*u.2) :
    ∀ᶠ w : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 0,
      w.1.1 = w.2.1 → F w.1 = F w.2 → w.1.2 = w.2.2 := by
  apply nearby_fiber_injective F p hF hb
  intro z
  have h₀ := hlin (0,0)
  have hz := hlin (0,z)
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, mul_zero, add_zero] at h₀ hz
  have he : (fun _ : Fin 0 => ((0,z) : ℝ × ℝ)) = (fun _ : Fin 0 => ((0,0) : ℝ × ℝ)) :=
    funext Fin.elim0
  rw [he] at hz
  have hzero : p 1 (fun _ => ((0,0) : ℝ × ℝ)) = 0 := (p 1).map_coord_zero 0 rfl
  linarith

end GaussianChains.Bifurcation
