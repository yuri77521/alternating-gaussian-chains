import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Width-eight Gaussian image derivatives and their uniform truncation error.
We use real-space images at the rational floors to avoid rounding π or evaluating
Chebyshev polynomials at rounded angles. -/
noncomputable section
namespace GaussianChains.Bifurcation.Images
open scoped BigOperators

inductive Order | value | first | second | third | fourth
  deriving DecidableEq

def polynomial {R : Type*} [CommRing R] (o : Order) (x : R) : R :=
  match o with
  | .value => 1
  | .first => -16*x
  | .second => 256*x^2-16
  | .third => 768*x-4096*x^3
  | .fourth => 65536*x^4-24576*x^2+768

def next : Order → Order
  | .value => .first
  | .first => .second
  | .second => .third
  | .third => .fourth
  | .fourth => .fourth

def term (o : Order) (x : ℝ) (k : ℤ) :=
  polynomial o (x+k) * Real.exp (-8*(x+k)^2)

def kernelD (o : Order) (x : ℝ) := ∑' k, term o x k

theorem term_hasDerivAt (o : Order) (ho : o ≠ .fourth) (x : ℝ) (k : ℤ) :
    HasDerivAt (fun y => term o y k) (term (next o) x k) x := by
  have hx := (hasDerivAt_id' x).add_const (k:ℝ)
  have he := ((hx.pow 2).const_mul (-8)).exp
  cases o
  · convert he using 1 <;> simp [term, polynomial, next, Pi.pow_apply] <;> ring
  · convert (hx.const_mul (-16)).mul he using 1 <;> dsimp [term, polynomial, next] <;> ring
  · convert (((hx.pow 2).const_mul 256).sub_const 16).mul he using 1 <;> dsimp [term, polynomial, next] <;> ring
  · convert ((hx.const_mul 768).sub ((hx.pow 3).const_mul 4096)).mul he using 1 <;> dsimp [term, polynomial, next] <;> ring
  · contradiction

private theorem polynomial_norm (o : Order) (u : ℝ) :
    |polynomial o u| ≤ 100000 * (Real.exp |u|)^4 := by
  let e := Real.exp |u|
  have he : 1 ≤ e := Real.one_le_exp (abs_nonneg _)
  have hu : |u| ≤ e := by dsimp [e]; linarith [Real.add_one_le_exp |u|]
  have hpow (j : ℕ) (hj : j ≤ 4) : |u^j| ≤ e^4 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) hu _).trans (pow_le_pow_right₀ he hj)
  have h1 : 1 ≤ e^4 := one_le_pow₀ he
  have H := abs_le.mp (by simpa using hpow 1 (by decide))
  have H₂ := abs_le.mp (hpow 2 (by decide))
  have H₃ := abs_le.mp (hpow 3 (by decide))
  have H₄ := abs_le.mp (hpow 4 (by decide))
  change |polynomial o u| ≤ 100000 * e^4
  rw [abs_le]
  cases o <;> dsimp [polynomial] <;> constructor <;> linarith

def tail (n : ℕ) : ℝ := 100000 * (1/2:ℝ)^112 * (1/2:ℝ)^n

private theorem bound_large (o : Order) (x : ℝ) (k : ℤ) (n : ℕ)
    (hh : 4 + (n:ℝ) ≤ |x+k|) : ‖term o x k‖ ≤ tail n := by
  let u := x+(k:ℝ)
  have ha : 4 ≤ |u| := by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hexp : 4*|u|-8*u^2 ≤ -112 - (n:ℝ) := by
    change 4+(n:ℝ) ≤ |u| at hh
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith : 0 ≤ |u|+4), sq_abs u]
  have hbase : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  have hbound : Real.exp (-112-(n:ℝ)) ≤ (1/2:ℝ)^112 * (1/2:ℝ)^n := by
    rw [show -112-(n:ℝ)=((112:ℕ):ℝ)*(-1)+(n:ℝ)*(-1) by push_cast; ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le hbase _)
      (pow_le_pow_left₀ (Real.exp_pos _).le hbase _) (by positivity) (by positivity)
  change ‖polynomial o u * Real.exp (-8*u^2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 100000 * (Real.exp |u|)^4 * Real.exp (-8*u^2) :=
      mul_le_mul_of_nonneg_right (polynomial_norm o u) (Real.exp_pos _).le
    _ = 100000 * Real.exp (4*|u|-8*u^2) := by
      rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2; push_cast; ring
    _ ≤ 100000 * ((1/2:ℝ)^112*(1/2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hexp).trans hbound) (by norm_num)
    _ = tail n := by unfold tail; ring

def radius : ℚ := 1/10^25

theorem finite_error (o : Order) {x : ℝ} (hx : |x| ≤ 1) :
    |kernelD o x - ∑ k ∈ Finset.Icc (-4:ℤ) 4, term o x k| ≤ (radius : ℝ) := by
  let ap := fun n : ℕ => term o x ((n:ℤ)+5)
  let am := fun n : ℕ => term o x (-((n:ℤ)+5))
  have hp (n : ℕ) : ‖ap n‖ ≤ tail n := by
    apply bound_large
    exact le_trans (by push_cast; linarith [(abs_le.mp hx).1]) (le_abs_self _)
  have hm (n : ℕ) : ‖am n‖ ≤ tail n := by
    apply bound_large
    exact le_trans (by push_cast; linarith [(abs_le.mp hx).2]) (neg_le_abs _)
  have hg := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have ht : Summable tail := hg.mul_left _
  have hsum : ∑' n, tail n = 200000*(1/2:ℝ)^112 := by
    simp only [tail, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]
    ring
  have bound {f : ℕ → ℝ} (H : ∀ n, ‖f n‖ ≤ tail n) :
      Summable f ∧ |∑' n, f n| ≤ 200000*(1/2:ℝ)^112 := by
    have S : Summable f := Summable.of_norm_bounded ht H
    refine ⟨S,?_⟩
    rw [← Real.norm_eq_abs, ← hsum]
    have Sn : Summable (fun n => ‖f n‖) := .of_nonneg_of_le (fun _ => norm_nonneg _) H ht
    exact (norm_tsum_le_tsum_norm Sn).trans (Sn.tsum_le_tsum H ht)
  obtain ⟨sp,bp⟩ := bound hp
  obtain ⟨sm,bm⟩ := bound hm
  have hp' : Summable (fun n : ℕ => term o x (n:ℤ)) :=
    (summable_nat_add_iff 5).mp (by simpa [ap] using sp)
  have hm' : Summable (fun n : ℕ => term o x (-((n:ℤ)+1))) :=
    (summable_nat_add_iff 4).mp (by simpa [am, add_assoc] using sm)
  unfold kernelD
  rw [tsum_of_nat_of_neg_add_one hp' hm', ← hp'.sum_add_tsum_nat_add 5,
    ← hm'.sum_add_tsum_nat_add 4]
  have hc : Finset.Icc (-4:ℤ) 4 = {-4,-3,-2,-1,0,1,2,3,4} := by decide
  have heal : (∑ n ∈ Finset.range 5, term o x (n:ℤ)) +
      (∑ n ∈ Finset.range 4, term o x (-((n:ℤ)+1))) =
      ∑ k ∈ Finset.Icc (-4:ℤ) 4, term o x k := by
    simp [hc, Finset.sum_range_succ]
    ring
  rw [← heal]
  have hr := abs_add_le (∑' n, ap n) (∑' n, am n)
  have hvalue : 200000*(1/2:ℝ)^112 + 200000*(1/2:ℝ)^112 ≤ (radius:ℝ) := by norm_num [radius]
  have hb := hr.trans ((add_le_add bp bm).trans hvalue)
  convert hb using 2 <;> simp [ap, am, add_assoc] <;> ring

private def major (k : ℤ) : ℝ :=
  if k.natAbs < 5 then 100000*(Real.exp 6)^4 else tail (k.natAbs-5)

private theorem pos_major (n : ℕ) : major ((n:ℤ)+5) = tail n := by
  change (if (n+5:ℕ) < 5 then _ else tail (n+5-5)) = _
  simp

private theorem neg_major (n : ℕ) : major (-((n:ℤ)+5)) = tail n := by
  unfold major
  rw [Int.natAbs_neg]
  exact pos_major n

private theorem major_summable : Summable major := by
  have ht : Summable tail :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  apply Summable.of_nat_of_neg_add_one
  · apply (summable_nat_add_iff 5).1
    simpa [Nat.cast_add, pos_major] using ht
  · apply (summable_nat_add_iff 4).1
    refine ht.congr (fun n => ?_)
    rw [← neg_major n]
    congr 2

private theorem uniform_image_bound (o : Order) {x : ℝ} (hx : |x| ≤ 1) (k : ℤ) :
    ‖term o x k‖ ≤ major k := by
  have hac : (k.natAbs:ℝ) = |(k:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  unfold major
  split_ifs with hk
  · have hkn : (k.natAbs:ℝ) < 5 := by exact_mod_cast hk
    have hu : |x+(k:ℝ)| ≤ 6 := by linarith [abs_add_le x (k:ℝ)]
    have hx' : Real.exp (-8*(x+k)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x+k)])
    rw [term,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply (mul_le_of_le_one_right (abs_nonneg _) hx').trans
    exact (polynomial_norm o _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hu) 4) (by norm_num))
  · apply bound_large
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat, hac]
    have hdiff := abs_add_le (x + (k:ℝ)) (-x)
    rw [show x + (k:ℝ) + -x = (k:ℝ) by ring, abs_neg] at hdiff
    linarith

/-- Termwise differentiation through fourth order on the interval used for the
critical cell, with one uniform summable majorant for all five functions. -/
theorem kernelD_hasDerivAt (o : Order) (ho : o ≠ .fourth) {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    HasDerivAt (kernelD o) (kernelD (next o) x) x := by
  apply hasDerivAt_tsum_of_isPreconnected (u := major) (t := Set.Ioo (-1:ℝ) 1)
    (y₀ := 0) major_summable isOpen_Ioo isPreconnected_Ioo (fun k y _ => term_hasDerivAt o ho y k)
  · exact fun k y hy => uniform_image_bound _ (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) k
  · constructor <;> norm_num
  · exact .of_norm_bounded major_summable (fun k => uniform_image_bound _ (by norm_num : |(0:ℝ)| ≤ 1) k)
  · exact hx

end GaussianChains.Bifurcation.Images
