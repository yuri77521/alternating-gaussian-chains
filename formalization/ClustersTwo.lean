import ChainGeometry
import ClustersWidth
import KernelFourier
import ChainEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Strict two-site antipodal comparison for the full Gaussian width condition. -/

noncomputable section

namespace GaussianChains

open Real

/-- Multiplying an angle by a natural number increases its sine modulus
by at most that factor. -/
theorem abs_sin_nat_mul_le (n : ℕ) (t : ℝ) :
    |sin (n * t)| ≤ n * |sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc
      _ ≤ |sin (n * t) * cos t| + |cos (n * t) * sin t| := abs_add_le _ _
      _ ≤ |sin (n * t)| * 1 + 1 * |sin t| := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (abs_nonneg _))
      _ ≤ (n + 1 : ℝ) * |sin t| := by linarith

/-- The chord deficit is quadratic, even at a multiple of a full turn. -/
theorem one_sub_cos_nat_mul_le (n : ℕ) (t : ℝ) :
    1 - cos (n * t) ≤ (n : ℝ)^2 * (1 - cos t) := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_sin_nat_mul_le n (t/2)) 2
  rw [mul_pow, sq_abs, sq_abs] at h
  have half (z : ℝ) : 1 - cos z = 2 * sin (z / 2)^2 := by
    have hz := cos_two_mul (z / 2)
    rw [show 2 * (z/2) = z by ring] at hz
    nlinarith [sin_sq_add_cos_sq (z/2)]
  rw [half, half, show (n : ℝ)*t / 2 = n*(t/2) by ring]
  nlinarith only [h]

/-- For a mode of order n the loss relative to the half turn is controlled
by the first-mode gain, independently of the parity of n. -/
theorem cos_half_turn_mode_loss (n : ℕ) (θ : ℝ) :
    cos (n * π) - cos (n * θ) ≤ (n : ℝ)^2 * (1 + cos θ) := by
  have h := one_sub_cos_nat_mul_le n (π-θ)
  rw [mul_sub, cos_nat_mul_pi_sub, cos_pi_sub] at h
  rw [cos_nat_mul_pi]
  rcases neg_one_pow_eq_or ℝ n with hsign | hsign
  · rw [hsign] at h ⊢
    linarith
  · rw [hsign]
    have hp : 0 ≤ 1 + cos θ := by linarith [neg_one_le_cos θ]
    nlinarith only [neg_one_le_cos (n * θ), mul_nonneg (sq_nonneg (n : ℝ)) hp]


def pairMode (q θ : ℝ) (k : ℕ) :=
  q^((k+1)^2) * cos (((k+1:ℕ):ℝ) * θ)

private theorem summable_pairMode {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (θ : ℝ) :
    Summable (pairMode q θ) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded
  intro k
  rw [pairMode, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
  calc
    _ ≤ q ^ ((k+1)^2) * 1 :=
      mul_le_mul_of_nonneg_left (abs_cos_le_one _) (pow_nonneg hq0 _)
    _ ≤ q ^ k := by
      rw [mul_one]
      apply pow_le_pow_of_le_one hq0 hq1.le
      nlinarith [Nat.zero_le (k^2)]

/-- The first Fourier mode leaves a strict gap after bounding every loss by the
actual infinite fourth moment R(q). The argument is independent of the floor. -/
theorem two_site_cosine_series_lt {q θ : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1)
    (hR : widthR q ≤ 2/3) (hθ : 0 < 1 + cos θ) :
    (∑' k, pairMode q π k) < ∑' k, pairMode q θ k := by
  let A := q * (1 + cos θ)
  have hA : 0 < A := mul_pos hq₀ hθ
  have hterm (k : ℕ) : pairMode q π (k+1) - pairMode q θ (k+1) ≤ widthTerm q k * A := by
    let n := k + 2
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
    have hpow : (n:ℝ)^2 ≤ (n:ℝ)^4 := by
      calc
        (n:ℝ)^2 ≤ (n:ℝ)^2 * (n:ℝ)^2 := le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
        _ = _ := by ring
    have hp : q^(n^2) = q^(n^2-1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n^2 by change 0 < (k+2)^2; positivity)]
    change q^(n^2) * cos ((n : ℝ)*π) - q^(n^2) * cos ((n:ℝ)*θ) ≤
      ((n:ℝ)^4 * q^(n^2-1)) * A
    rw [← mul_sub]
    calc
      _ ≤ q^(n^2) * ((n:ℝ)^2 * (1 + cos θ)) :=
        mul_le_mul_of_nonneg_left (cos_half_turn_mode_loss n θ) (pow_nonneg hq₀.le _)
      _ ≤ q^(n^2) * ((n:ℝ)^4 * (1 + cos θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hθ.le) (pow_nonneg hq₀.le _)
      _ = _ := by rw [hp]; dsimp [A]; ring
  have hs := summable_pairMode hq₀.le hq₁
  have hp := (summable_nat_add_iff 1).2 (hs π)
  have ht := (summable_nat_add_iff 1).2 (hs θ)
  have hr := ((summable_widthTerm hq₀.le hq₁).hasSum.mul_right A)
  have htail := (hp.sub ht).tsum_le_tsum hterm hr.summable
  rw [hp.tsum_sub ht, hr.tsum_eq] at htail
  rw [(hs π).tsum_eq_zero_add, (hs θ).tsum_eq_zero_add]
  change pairMode q π 0 + _ < pairMode q θ 0 + _
  simp only [pairMode, Nat.zero_add, Nat.one_pow, pow_one, Nat.cast_one, one_mul, cos_pi,
    mul_neg_one] at *
  change _ ≤ widthR q * A at htail
  have hlt : widthR q * A < A := by nlinarith only [mul_le_mul_of_nonneg_right hR hA.le, hA]
  dsimp [A] at htail hlt
  linarith

private theorem kernel_eq_pair_series {s : ℝ} (hs : 0 < s) (d : ℝ) :
    kernel s d = sqrt (π / s) * (1 + 2 * ∑' n,
      pairMode (exp (-(π^2)/s)) (2*π*d) n) := by
  rw [kernel_fourier hs]
  unfold pairMode
  simp_rw [show ∀ n : ℕ, 2 * π * ((n+1 : ℕ) : ℝ) * d =
    ((n+1 : ℕ) : ℝ) * (2*π*d) by intro n; ring]

private theorem kernel_even_of_pos {s : ℝ} (hs : 0 < s) (d : ℝ) :
    kernel s (-d) = kernel s d := by
  rw [kernel_eq_pair_series hs, kernel_eq_pair_series hs]
  simp [pairMode, mul_neg, cos_neg]

/-- Under the paper's full width assumption the periodized kernel has a unique
minimum at separation 1/2 throughout one closed period. -/
theorem kernel_half_strict {s d : ℝ} (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (hne : d ≠ 1/2) :
    kernel s (1/2) < kernel s d := by
  let θ := 2*π*d
  have hθ : 0 < 1 + cos θ := by
    have hpi := pi_pos
    have hπd := mul_nonneg hpi.le hd₀
    have hπd' := mul_le_mul_of_nonneg_left hd₁ hpi.le
    have h (t : ℝ) (h₁ : 0 ≤ t) (h₂ : t < π) : 0 < 1 + cos t := by
      have hc := cos_lt_cos_of_nonneg_of_le_pi h₁ (le_refl π) h₂
      rw [cos_pi] at hc
      linarith
    rcases lt_or_gt_of_ne hne with hd | hd
    · apply h
      · dsimp [θ]; positivity
      · dsimp [θ]; nlinarith [mul_pos hpi (sub_pos.mpr hd)]
    · rw [← cos_two_pi_sub θ]
      apply h <;> dsimp [θ] <;> nlinarith [mul_pos hpi (sub_pos.mpr hd)]
  have hq : exp (-(π^2)/s) < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (pow_pos pi_pos 2)) hs)
  have h := two_site_cosine_series_lt (exp_pos _) hq hR hθ
  have ht : 2*π*(1/2 : ℝ) = π := by ring
  rw [kernel_eq_pair_series hs, kernel_eq_pair_series hs, ht]
  exact mul_lt_mul_of_pos_left (by dsimp [θ] at h; linarith) (sqrt_pos.mpr (div_pos pi_pos hs))

theorem two_imageEnergy_eq {s : ℝ} (hs : 0 < s) (x : Fin 2 → ℝ) :
    imageEnergy s x = 1 - kernel s 0 + kernel s (x 1 - x 0) := by
  unfold imageEnergy
  simp [Fin.sum_univ_two, charge]
  rw [show x 0 - x 1 = -(x 1 - x 0) by ring, kernel_even_of_pos hs]
  ring

/-- Label zero is positive. Every admissible two-site cell has energy at least
that of any antipodal pair, with equality exactly on its translation orbit.
The inequalities include both cyclic gaps and allow the closed endpoint h=1/2. -/
theorem two_antipodal_minimizes_iff {s h : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (h₀ : 0 ≤ h)
    (x p : Fin 2 → ℝ) (hp : p 1 - p 0 = 1/2)
    (hg₀ : h ≤ x 1 - x 0) (hg₁ : h ≤ 1 - (x 1 - x 0)) :
    imageEnergy s p ≤ imageEnergy s x ∧
    (imageEnergy s p = imageEnergy s x ↔ ∃ t : ℝ, ∀ i, x i = p i + t) := by
  have hiff : (∃ t : ℝ, ∀ i, x i = p i + t) ↔ x 1 - x 0 = 1/2 := by
    constructor
    · rintro ⟨t, ht⟩
      rw [ht 0, ht 1]
      linarith
    · intro hgap
      refine ⟨x 0 - p 0, ?_⟩
      intro i
      refine Fin.cases (by ring) (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change x 1 = p 1 + (x 0 - p 0)
      linarith
  rw [hiff, two_imageEnergy_eq hs p, two_imageEnergy_eq hs x, hp]
  by_cases heq : x 1 - x 0 = 1/2
  · simp [heq]
  · have hlt := kernel_half_strict hs hR (h₀.trans hg₀) (by linarith) heq
    exact ⟨by linarith, ⟨fun he => False.elim (by linarith), fun hf => False.elim (heq hf)⟩⟩

def antipodalPair : Fin 2 → ℝ := fun i => (i.val : ℝ) / 2

private theorem two_feasible_iff (h : ℝ) (x : Fin 2 → ℝ) :
    Feasible (by decide) h x ↔ h ≤ x 1 - x 0 ∧ h ≤ 1 - (x 1 - x 0) := by
  have h0 := gap_interior (by decide : 0 < 2) x 0 (by decide)
  have h1 := gap_wrap (by decide : 0 < 2) x 1 (by decide)
  change gap _ x 0 = x 1 - x 0 at h0
  change gap _ x 1 = x 0 + 1 - x 1 at h1
  constructor
  · intro hx
    have h₀ := hx 0
    have h₁ := hx 1
    rw [h0] at h₀
    rw [h1] at h₁
    exact ⟨h₀, by linarith⟩
  · rintro ⟨h₀, h₁⟩ i
    refine Fin.cases (h0.symm ▸ h₀) (fun j => ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change h ≤ gap _ x 1
    linarith

/-- The two-site clause of Theorem 1 on the general cyclic configuration space.
The comparison quantifies every feasible cell. Translation gives the complete
orbit of minimizers, even when the two cyclic gaps are both at the floor. -/
theorem two_site_classification {s h : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (h₀ : 0 ≤ h) (h₁ : h ≤ 1/2) :
    Feasible (by decide) h antipodalPair ∧
    ∀ x : Fin 2 → ℝ, Feasible (by decide) h x →
      ((∀ y : Fin 2 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y) ↔
        ∃ t : ℝ, ∀ i, x i = antipodalPair i + t) := by
  have hp : antipodalPair 1 - antipodalPair 0 = 1/2 := by norm_num [antipodalPair]
  have hpFeas : Feasible (by decide) h antipodalPair := by
    rw [two_feasible_iff, hp]
    exact ⟨h₁, by linarith⟩
  have cmp (x : Fin 2 → ℝ) (hx : Feasible (by decide) h x) :=
    two_antipodal_minimizes_iff hs hR h₀ x antipodalPair hp
      ((two_feasible_iff _ _).1 hx).1 ((two_feasible_iff _ _).1 hx).2
  refine ⟨hpFeas, ?_⟩
  intro x hx
  constructor
  · intro hmin
    exact (cmp x hx).2.mp (le_antisymm (cmp x hx).1 (hmin _ hpFeas))
  · intro horbit y hy
    rw [← (cmp x hx).2.mpr horbit]
    exact (cmp y hy).1

#print axioms two_site_classification

end GaussianChains