import ChainFourier
import ChainGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The occupied intervals go from each positive label to the immediately
following negative label. Half-open intervals keep all unions disjoint even
when a gap vanishes. Fourier integrals are in angular units. -/

noncomputable section
namespace GaussianChains.Occupation
open Real MeasureTheory Finset Set

def angle {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (j : ℕ) : ℝ :=
  2 * π * liftSite hN x j

theorem angle_monotone {N : ℕ} {hN : 0 < N} {x : Fin N → ℝ} (hx : Feasible hN 0 x) :
    Monotone (angle hN x) := by
  apply monotone_nat_of_le_succ
  intro k
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*π)
  have H := hx ⟨k%N, Nat.mod_lt _ hN⟩
  rw [← gap_lift_period] at H
  linarith

theorem angle_period {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (j : ℕ) :
    angle hN x (j+N) = angle hN x j + 2*π := by
  simp [angle, liftSite_add_period, mul_add]

def arc {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) (r : ℕ) : Set ℝ :=
  Ioc (angle hN x (2*r)) (angle hN x (2*r+1))

def inCell {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) : Set ℝ :=
  ⋃ r ∈ range m, arc hN x r

theorem measurable_inCell {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) :
    MeasurableSet (inCell hN x) :=
  (range m).measurableSet_biUnion fun _ _ => measurableSet_Ioc

theorem inCell_subset {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} (hx : Feasible hN 0 x) :
    inCell hN x ⊆ Ioc (angle hN x 0) (angle hN x 0 + 2*π) := by
  intro y hy
  obtain ⟨r,hr,hr'⟩ := mem_iUnion₂.1 hy
  have hrm := mem_range.1 hr
  have hupper : angle hN x (2*r+1) ≤ angle hN x (0+2*m) := angle_monotone hx (by omega)
  rw [angle_period] at hupper
  exact ⟨lt_of_le_of_lt (angle_monotone hx (Nat.zero_le _)) hr'.1, hr'.2.trans hupper⟩

private def wave (n : ℕ) (t : ℝ) : ℂ := Complex.exp (((n:ℂ)*Complex.I) * (t:ℂ))

private theorem wave_continuous (n : ℕ) : Continuous (wave n) := by unfold wave; fun_prop

private theorem wave_integral (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    -((n:ℂ)*Complex.I) * (∫ t in a..b, wave n t) = wave n a - wave n b := by
  have h : (n:ℂ)*Complex.I ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') Complex.I_ne_zero
  unfold wave
  rw [integral_exp_mul_complex h]
  rw [neg_mul, mul_comm ((n:ℂ)*Complex.I) _, div_mul_cancel₀ _ h, neg_sub]

private theorem sum_pairs (m : ℕ) (f : ℕ → ℂ) :
    ∑ k ∈ range (2*m), (-1:ℂ)^k * f k = ∑ r ∈ range m, (f (2*r) - f (2*r+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    simp [pow_add, pow_mul, sub_eq_add_neg, add_assoc]

private theorem structureFactor_pairs {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) (n : ℕ) :
    structureFactor x n = ∑ r ∈ range m, (wave n (angle hN x (2*r)) -
      wave n (angle hN x (2*r+1))) := by
  rw [← sum_pairs m (fun k => wave n (angle hN x k)), ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  unfold charge wave angle
  rw [liftSite_fin]
  push_cast
  congr 2
  ring

/-- Integration by parts for the actual jump measure of the cell. Both sides
include every label, including cancelling labels at a collision. -/
theorem structureFactor_eq_integral {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) (n : ℕ) (hn : 0 < n) :
    structureFactor x n = -((n:ℂ)*Complex.I) *
      ∫ t in inCell hN x, Complex.exp (((n:ℂ)*Complex.I) * (t:ℂ)) := by
  change _ = _ * ∫ t in inCell hN x, wave n t
  have hd : Set.Pairwise ((range m : Finset ℕ) : Set ℕ) (fun i j => Disjoint (arc hN x i) (arc hN x j)) := by
    intro r hr j hj hrj
    rcases lt_or_gt_of_ne hrj with h | h
    · exact Ioc_disjoint_Ioc_of_le (angle_monotone hx (by omega : 2*r+1 ≤ 2*j))
    · exact (Ioc_disjoint_Ioc_of_le (angle_monotone hx (by omega : 2*j+1 ≤ 2*r))).symm
  have hi (r : ℕ) : IntegrableOn (wave n) (arc hN x r) :=
    ((wave_continuous n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [inCell, integral_biUnion_finset (s := arc hN x) (range m) (fun _ _ => measurableSet_Ioc) hd (fun r _ => hi r),
    Finset.mul_sum, structureFactor_pairs hN]
  apply sum_congr rfl
  intro r _
  have hab := angle_monotone hx (Nat.le_succ (2*r))
  rw [← wave_integral n hn, intervalIntegral.integral_of_le hab] <;> rfl

/-- Periodic extension of the occupied arcs. Its restriction to the fundamental
cell coincides with the finite union inCell. -/
def circleSet {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) : Set ℝ :=
  ⋃ k : ℤ, (fun t : ℝ => t - (k:ℝ)*(2*π)) ⁻¹' inCell hN x

theorem mem_circleSet_iff {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} {t : ℝ} :
    t ∈ circleSet hN x ↔ ∃ k : ℤ, t - (k:ℝ)*(2*π) ∈ inCell hN x :=
  mem_iUnion

theorem measurable_circleSet {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) :
    MeasurableSet (circleSet hN x) := by
  apply MeasurableSet.iUnion
  intro k
  exact (measurable_inCell hN x).preimage (measurable_id.sub measurable_const)

theorem circleSet_periodic {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) (t : ℝ) :
    t+2*π ∈ circleSet hN x ↔ t ∈ circleSet hN x := by
  rw [mem_circleSet_iff, mem_circleSet_iff]
  constructor
  · rintro ⟨k,h⟩
    refine ⟨k-1,?_⟩
    convert h using 1 <;> push_cast <;> ring
  · rintro ⟨k,h⟩
    refine ⟨k+1,?_⟩
    convert h using 1 <;> push_cast <;> ring

theorem inter_circleSet {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} (hx : Feasible hN 0 x) :
    Ioc (angle hN x 0) (angle hN x 0+2*π) ∩ circleSet hN x = inCell hN x := by
  ext y
  constructor
  · rintro ⟨hy,hc⟩
    obtain ⟨k,hk⟩ := mem_circleSet_iff.1 hc
    have ht := inCell_subset hx hk
    rcases lt_trichotomy k 0 with h | rfl | h
    · have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hb := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2*π by positivity)
      linarith [hy.1,ht.2]
    · simpa using hk
    · have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hb := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2*π by positivity)
      linarith [hy.2,ht.1]
  · intro hy
    exact ⟨inCell_subset hx hy,mem_circleSet_iff.2 ⟨0,by simpa using hy⟩⟩

private theorem wave_periodic (n : ℕ) : Function.Periodic (wave n) (2*π) := by
  intro t
  unfold wave
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have ht : ((n:ℂ)*Complex.I) * ((2*π:ℝ):ℂ) = n * (2*π*Complex.I) := by push_cast; ring
  rw [ht, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The cut used for the Fourier integral is arbitrary; in particular it can
be fixed at zero after translating the sites to align the first mode. -/
theorem structureFactor_eq_periodicIntegral {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) (n : ℕ) (hn : 0 < n) :
    structureFactor x n = -((n:ℂ)*Complex.I) *
      ∫ t in 0..2*π, (circleSet hN x).indicator
        (fun u : ℝ => Complex.exp (((n:ℂ)*Complex.I) * (u:ℂ))) t := by
  change _ = _ * ∫ t in 0..2*π, (circleSet hN x).indicator (wave n) t
  have hp : Function.Periodic ((circleSet hN x).indicator (wave n)) (2*π) := by
    intro t
    by_cases ht : t ∈ circleSet hN x
    · simp [ht, (circleSet_periodic hN x t).2 ht, wave_periodic n t]
    · simp [ht, (circleSet_periodic hN x t).not.2 ht]
  have shift := hp.intervalIntegral_add_eq 0 (angle hN x 0)
  rw [zero_add] at shift
  rw [shift, intervalIntegral.integral_of_le (by linarith [pi_pos]),
    setIntegral_indicator (measurable_circleSet hN x), inter_circleSet hx]
  exact structureFactor_eq_integral hx n hn

end GaussianChains.Occupation
