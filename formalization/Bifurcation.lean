import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Release and critical-point estimates for Proposition 4. The four variables are
the excess gaps numbered 0, 1, 3 and 4; the displacement is held fixed along each ray. -/

namespace GaussianChains.Bifurcation

open Set Filter
open scoped BigOperators Topology

abbrev Release := Fin 4 → ℝ

/-- Evaluate a derivative on a release vector by its four coordinate partials. -/
theorem release_derivative (D : Release →L[ℝ] ℝ) (u : Release) :
    D u = ∑ i, u i * D (Pi.single i 1) := by
  calc
    D u = D (∑ i, Pi.single i (u i)) := congrArg D (Finset.univ_sum_single u).symm
    _ = ∑ i, D (Pi.single i (u i)) := map_sum D _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have h : (Pi.single i (u i) : Release) = u i • (Pi.single i 1 : Release) := by
        ext j
        by_cases hji : j = i
        · subst j; simp
        · simp [Pi.single_eq_of_ne hji]
      rw [h, map_smul]
      rfl

/-- If each inward partial is at least γ on a release segment, the energy rise
from ru to u is at least (1−r)γ times the total opened length. -/
theorem release_segment (E : Release → ℝ) (u : Release) {γ r₀ : ℝ}
    (hr : r₀ < 1) (hu : ∀ i, 0 ≤ u i)
    (hD : ∀ r ∈ Icc r₀ 1, DifferentiableAt ℝ E (r • u))
    (hpartial : ∀ r ∈ Ioo r₀ 1, ∀ i, γ ≤ fderiv ℝ E (r • u) (Pi.single i 1)) :
    (1 - r₀) * γ * (∑ i, u i) ≤ E u - E (r₀ • u) := by
  let g := fun r : ℝ => E (r • u)
  have hd (r : ℝ) (h : r ∈ Icc r₀ 1) :
      HasDerivAt g (fderiv ℝ E (r • u) u) r := by
    have hr : HasDerivAt (fun k : ℝ => k • u) u r := by
      simpa using (hasDerivAt_id' r).smul_const u
    exact (hD r h).hasFDerivAt.comp_hasDerivAt r hr
  obtain ⟨c, hc, hval⟩ := exists_hasDerivAt_eq_slope g
    (fun r => fderiv ℝ E (r • u) u) hr
    (fun r h => (hd r h).continuousAt.continuousWithinAt)
    (fun r h => hd r (Ioo_subset_Icc_self h))
  have hsum : γ * (∑ i, u i) ≤ fderiv ℝ E (c • u) u := by
    rw [release_derivative, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_comm γ]
      exact mul_le_mul_of_nonneg_left (hpartial c hc i) (hu i)
  rw [hval, le_div_iff₀ (sub_pos.mpr hr)] at hsum
  simpa [g, mul_comm, mul_assoc, mul_left_comm] using hsum

/-- Every nonempty release has strictly positive total size. -/
theorem total_release_pos {u : Release} (hu : ∀ i, 0 ≤ u i) (hne : u ≠ 0) :
    0 < ∑ i, u i := by
  have he : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨j, hj⟩ := he
  exact Finset.sum_pos' (fun i _ => hu i) ⟨j, Finset.mem_univ _, lt_of_le_of_ne (hu j) hj.symm⟩

/-- A nonzero release admits arbitrarily small feasible contractions that decrease
energy. Parameter distance can be made arbitrarily small on the same release ray. -/
theorem smaller_release (E : Release → ℝ) {γ : ℝ} (hγ : 0 < γ)
    {u : Release} (hu : ∀ i, 0 ≤ u i) (hne : u ≠ 0)
    (hD : ∀ r ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ E (r • u))
    (hpartial : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, γ ≤ fderiv ℝ E (r • u) (Pi.single i 1)) :
    ∀ ε > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) 1, 1 - r < ε ∧ E (r • u) < E u := by
  intro ε hε
  let r₀ := 1 - min (ε / 2) (1 / 2 : ℝ)
  have h₀ : 0 < r₀ := by dsimp [r₀]; linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
  have h₁ : r₀ < 1 := by dsimp [r₀]; linarith [lt_min (show 0 < ε / 2 by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)]
  refine ⟨r₀, ⟨h₀, h₁⟩, ?_, ?_⟩
  · dsimp [r₀]; linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  · have h := release_segment E u h₁ hu
      (fun r h => hD r ⟨h₀.le.trans h.1, h.2⟩)
      (fun r h => hpartial r ⟨h₀.trans h.1, h.2⟩)
    have hp := mul_pos (mul_pos (sub_pos.mpr h₁) hγ) (total_release_pos hu hne)
    linarith

/-- This applies equally at a degenerate quartic face minimum and at a
nondegenerate face minimum: the four independent releases contribute linearly. -/
theorem strict_min_with_releases (E : ℝ → Release → ℝ) {t : ℝ} {u : Release} {γ : ℝ}
    (hγ : 0 < γ) (hu : ∀ i, 0 ≤ u i)
    (hD : ∀ r ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (E t) (r • u))
    (hpartial : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, γ ≤ fderiv ℝ (E t) (r • u) (Pi.single i 1))
    (hface : t ≠ 0 → E 0 0 < E t 0) (hne : t ≠ 0 ∨ u ≠ 0) :
    E 0 0 < E t u := by
  have h := release_segment (E t) u zero_lt_one hu hD hpartial
  simp only [sub_zero, one_mul, zero_smul] at h
  by_cases ht : t = 0
  · subst t
    have hp := mul_pos hγ (total_release_pos hu (hne.resolve_left (not_not_intro rfl)))
    linarith
  · have hn : 0 ≤ γ * ∑ i, u i :=
      mul_nonneg hγ.le (Finset.sum_nonneg (fun i _ => hu i))
    linarith [hface ht]

/-- Exact propagation of the rational enclosures for A and B at the critical root. -/
theorem coefficient_intervals {A B : ℝ}
    (hA₁ : -58.94248 < A) (hA₂ : A < -58.94246)
    (hB₁ : 70.22242 < B) (hB₂ : B < 70.22244) :
    (2.24414 < Real.sqrt (-6*A/B) ∧ Real.sqrt (-6*A/B) < 2.24416) ∧
    (74.2115 < 3*A^2/(2*B) ∧ 3*A^2/(2*B) < 74.2119) := by
  have hB : 0 < B := by linarith
  have ha : (58.94246:ℝ)^2 < A^2 := by
    nlinarith [mul_pos (by linarith : 0 < -A - 58.94246) (by linarith : 0 < -A + 58.94246)]
  have hb : A^2 < (58.94248:ℝ)^2 := by
    nlinarith [mul_pos (by linarith : 0 < 58.94248 + A) (by linarith : 0 < 58.94248 - A)]
  constructor
  · constructor
    · apply Real.lt_sqrt_of_sq_lt
      rw [lt_div_iff₀ hB]
      linarith
    · apply (Real.sqrt_lt' (by norm_num)).2
      rw [div_lt_iff₀ hB]
      linarith
  · constructor
    · rw [lt_div_iff₀ (by positivity)]
      linarith
    · rw [div_lt_iff₀ (by positivity)]
      linarith

/-- Continuity of the four release partials at the centered cell supplies one
neighborhood and one lower bound valid on every radial segment in it. -/
theorem uniform_release_neighborhood (E : ℝ → Release → ℝ)
    (D : ℝ → Release → Release →L[ℝ] ℝ) {γ : ℝ}
    (hD : ∀ t u, HasFDerivAt (E t) (D t u) u)
    (hcont : ∀ j : Fin 4, ContinuousAt
      (fun p : ℝ × Release => D p.1 p.2 (Pi.single j 1)) (0,0))
    (hp : ∀ j, γ < D 0 0 (Pi.single j 1)) :
    ∃ r > (0 : ℝ), ∀ t u, |t| < r → ‖u‖ < r → (∀ i, 0 ≤ u i) →
      γ * (∑ i, u i) ≤ E t u - E t 0 := by
  have he : ∀ᶠ p : ℝ × Release in 𝓝 (0,0), ∀ j, γ < D p.1 p.2 (Pi.single j 1) :=
    Filter.eventually_all.mpr fun j => (hcont j).eventually (lt_mem_nhds (hp j))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro t u ht hu hpos
  have h := release_segment (E t) u zero_lt_one hpos
    (fun a _ => (hD _ _).differentiableAt) (fun a ha j => by
      rw [(hD _ _).fderiv]
      apply le_of_lt
      apply hball (y := (t,a • u))
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha.1, max_lt_iff]
      exact ⟨ht, (mul_le_of_le_one_left (norm_nonneg _) ha.2.le).trans_lt hu⟩)
  simpa using h

end GaussianChains.Bifurcation
