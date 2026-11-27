import CertTreeKernelDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absolute tails for the seven-image kernel tables of Appendix A. -/

noncomputable section
namespace GaussianChains.ImageBounds

inductive Order | value | first | second
  deriving DecidableEq

/-- Values of the individual image and its first two spatial derivatives. -/
def image (j : Order) (s t : ℝ) : ℝ :=
  (match j with
    | .value => 1
    | .first => -2 * s * t
    | .second => (2 * s * t)^2 - 2*s) * Real.exp (-s * t^2)

private theorem exp_neg_nat (n : ℕ) :
    Real.exp (-(n:ℝ)) ≤ (1/2:ℝ)^n := by
  have h : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  simpa using (Real.exp_nat_mul (-1) n).le.trans
    (pow_le_pow_left₀ (Real.exp_pos _).le h n)

private theorem polynomial_growth (k : ℕ) : ((k:ℝ)+5)^2 ≤ 25 * 4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ, pow_succ (4:ℝ)]
    have hk : (0:ℝ) ≤ k := by positivity
    nlinarith [sq_nonneg (k:ℝ)]

private theorem shell_bound (j : Order) {s u t : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (has : (a:ℝ) ≤ s) (hsu : s ≤ u) (k : ℕ)
    (ht : (k:ℝ)+3 ≤ |t|) (ht' : |t| ≤ (k:ℝ)+5) :
    |image j s t| ≤ ((2*u)^2*25 + 2*u) * (1/2:ℝ)^(9*a) * (1/2:ℝ)^k := by
  have hk : (0:ℝ) ≤ k := by positivity
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hs : 0 ≤ s := by linarith
  have hu : 0 ≤ u := hs.trans hsu
  have hpow : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have ht2 : t^2 ≤ 25 * (4:ℝ)^k := by
    calc t^2 = |t|^2 := (sq_abs _).symm
         _ ≤ ((k:ℝ)+5)^2 := pow_le_pow_left₀ (abs_nonneg _) ht' 2
         _ ≤ _ := polynomial_growth k
  have htlo : (k:ℝ)^2 + 6*k + 9 ≤ t^2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (k:ℝ)+3) ht 2
    rw [sq_abs] at h
    nlinarith
  have hsexp : ((9*a+3*k:ℕ):ℝ) ≤ s*t^2 := by
    push_cast
    have h1 := mul_le_mul_of_nonneg_left htlo hs
    nlinarith [mul_nonneg hs (sq_nonneg (k:ℝ)), mul_nonneg (show 0 ≤ s-1 by linarith) hk]
  have he := (Real.exp_le_exp.mpr (neg_le_neg hsexp)).trans (exp_neg_nat _)
  have hst : |2*s*t| ≤ 2*u*|t| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*s)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hp2 : (2*s*t)^2 ≤ (2*u)^2 * (25*4^k) := by
    calc (2*s*t)^2 = |2*s*t|^2 := (sq_abs _).symm
         _ ≤ (2*u*|t|)^2 := pow_le_pow_left₀ (abs_nonneg _) hst 2
         _ = (2*u)^2*t^2 := by rw [mul_pow, sq_abs]
         _ ≤ _ := mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
  have hcoeff : |(match j with
    | .value => 1
    | .first => -2*s*t
    | .second => (2*s*t)^2-2*s)| ≤ ((2*u)^2*25+2*u)*4^k := by
    cases j with
    | value =>
      simp
      nlinarith [mul_nonneg (sq_nonneg (2*u)) (show 0 ≤ (4:ℝ)^k by positivity),
        mul_le_mul_of_nonneg_left hpow hu]
    | first =>
      simp only [neg_mul, abs_neg]
      nlinarith [sq_nonneg (|2*s*t|-1), sq_abs (2*s*t),
        mul_le_mul_of_nonneg_left hpow hu]
    | second =>
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (2*s*t),
        mul_le_mul_of_nonneg_left hpow hu, mul_nonneg (sq_nonneg (2*u)) (show 0 ≤ (4:ℝ)^k by positivity)]
  calc |image j s t| = _ := by
         unfold image
         simp only [abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
       _ ≤ (((2*u)^2*25+2*u)*4^k) * ((1/2:ℝ)^(9*a+3*k)) :=
         mul_le_mul hcoeff he (Real.exp_pos _).le (by positivity)
       _ = _ := by
         rw [pow_add, pow_mul (1/2:ℝ) 3 k]
         have htt : (4:ℝ)^k * ((1/2:ℝ)^3)^k = (1/2:ℝ)^k := by
           rw [← mul_pow]
           norm_num
         linear_combination ((2*u)^2*25+2*u)*(1/2:ℝ)^(9*a) * htt

/-- The retained entries are `0,1,2,3` and `−1,−2,−3`. -/
def seven (f : ℤ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range 4, f (k:ℤ)) + ∑ k ∈ Finset.range 3, f (-((k:ℤ)+1))

private theorem truncation {f : ℤ → ℝ} {C : ℝ}
    (hp : ∀ k : ℕ, |f ((k:ℤ)+4)| ≤ C*(1/2:ℝ)^k)
    (hn : ∀ k : ℕ, |f (-((k:ℤ)+4))| ≤ C*(1/2:ℝ)^k) :
    Summable f ∧ |(∑' k, f k) - seven f| ≤ 4*C := by
  have hg : Summable (fun k : ℕ => C*(1/2:ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have side {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ C*(1/2)^k) :
      Summable v ∧ |∑' k, v k| ≤ 2*C := by
    have h : Summable v := .of_norm_bounded hg (by simpa only [Real.norm_eq_abs] using hv)
    have hn : Summable (fun k => ‖v k‖) := .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by simpa only [Real.norm_eq_abs] using hv k) hg
    refine ⟨h, ?_⟩
    calc |∑' k, v k| ≤ ∑' k, |v k| := by
           simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
         _ ≤ ∑' k : ℕ, C*(1/2:ℝ)^k := by
           exact (by simpa only [Real.norm_eq_abs] using hn : Summable (fun k => |v k|)).tsum_le_tsum hv hg
         _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  obtain ⟨sp, bp⟩ := side hp
  obtain ⟨sn, bn⟩ := side hn
  let P : ℕ → ℝ := fun n => f n
  let N : ℕ → ℝ := fun n => f (-((n:ℤ)+1))
  have sp' : Summable P := (summable_nat_add_iff 4).mp (by simpa [P] using sp)
  have ns (k : ℕ) : N (k+3) = f (-((k:ℤ)+4)) := by
    dsimp [N]
    congr 2
  have sn' : Summable N := (summable_nat_add_iff 3).mp (by simpa only [ns] using sn)
  refine ⟨Summable.of_nat_of_neg_add_one sp' sn', ?_⟩
  have heq : (∑' n, f n) - seven f =
      (∑' k : ℕ, f ((k:ℤ)+4)) + ∑' k : ℕ, f (-((k:ℤ)+4)) := by
    rw [tsum_of_nat_of_neg_add_one sp' sn']
    change (∑' n, P n) + (∑' n, N n) - seven f = _
    rw [← sp'.sum_add_tsum_nat_add 4, ← sn'.sum_add_tsum_nat_add 3]
    simp only [ns, seven, P, N, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [heq]
  exact (abs_add_le ..).trans (by linarith)

/-- Uniform error of the seven-image approximation, for the value, slope or
curvature integrand. Both omitted half-lines are included. -/
theorem seven_image_error (j : Order) {s u x : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (has : (a:ℝ) ≤ s) (hsu : s ≤ u) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Summable (fun n : ℤ => image j s (x+n)) ∧
    |(∑' n : ℤ, image j s (x+n)) - seven (fun n => image j s (x+n))| ≤
      4*(((2*u)^2*25+2*u)*(1/2:ℝ)^(9*a)) := by
  obtain ⟨hx0,hx1⟩ := hx
  apply truncation
  · intro k
    push_cast
    apply shell_bound j ha has hsu k
    · rw [abs_of_nonneg (by positivity)]
      linarith
    · rw [abs_of_nonneg (by positivity)]
      linarith
  · intro k
    push_cast
    apply shell_bound j ha has hsu k
    · rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k])]
      linarith
    · rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k])]
      linarith

theorem strip_seven_image_error (j : Order) {s x : ℝ}
    (hs : s ∈ Set.Icc (8:ℝ) 9) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |(∑' n : ℤ, image j s (x+n)) - seven (fun n => image j s (x+n))| <
      1/(10:ℝ)^9 :=
  (seven_image_error j (a:=8) (by decide) hs.1 hs.2 hx).2.trans_lt (by norm_num)

theorem point_seven_image_error (j : Order) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |(∑' n : ℤ, image j 22 (x+n)) - seven (fun n => image j 22 (x+n))| <
      1/(10:ℝ)^11 :=
  (seven_image_error j (a:=22) (u:=22) (by decide) (by norm_num) le_rfl hx).2.trans_lt
    (by norm_num)

/-- The full integer periodization at a given derivative order. -/
def series (j : Order) (s x : ℝ) : ℝ := ∑' z : ℤ, image j s (x+z)

theorem seven_eq_Icc (f : ℤ → ℝ) : seven f = ∑ k ∈ Finset.Icc (-3:ℤ) 3, f k := by
  have hc : Finset.Icc (-3:ℤ) 3 = {-3,-2,-1,0,1,2,3} := by decide
  simp [seven, hc, Finset.sum_range_succ]
  ring

/-- Seven certified rational image intervals and the analytic tail imply a
real enclosure for the full value or derivative at the table node. -/
theorem enclose_seven (j : Order) {s u x : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (has : (a:ℝ) ≤ s) (hsu : s ≤ u) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ℤ → ℚ)
    (h : ∀ k ∈ Finset.Icc (-3:ℤ) 3, image j s (x+k) ∈ Set.Icc (lo k:ℝ) (hi k:ℝ)) :
    let err := 4*(((2*u)^2*25+2*u)*(1/2:ℝ)^(9*a))
    series j s x ∈ Set.Icc (((∑ k ∈ Finset.Icc (-3:ℤ) 3, lo k : ℚ):ℝ) - err)
      (((∑ k ∈ Finset.Icc (-3:ℤ) 3, hi k : ℚ):ℝ) + err) := by
  dsimp only
  push_cast
  have htail := abs_le.mp (seven_image_error j ha has hsu hx).2
  rw [seven_eq_Icc] at htail
  have hlo := Finset.sum_le_sum (fun k hk => (h k hk).1)
  have hhi := Finset.sum_le_sum (fun k hk => (h k hk).2)
  unfold series
  constructor <;> linarith [htail.1,htail.2]

/-- The zero-order series is exactly the kernel of the physical chain model. -/
theorem series_value_eq_kernel (s : ℝ) : series .value s = GaussianChains.kernel s := by
  funext x
  simp [series, image, GaussianChains.kernel]

open GaussianChains.ImageCalculus

private theorem series_first_eq (s : ℝ) : periodized s (next s 1) = series .first s := by
  funext x
  apply tsum_congr
  intro k
  simp [imageTerm, image, next]

private theorem series_second_eq (s : ℝ) : periodized s (next s (next s 1)) = series .second s := by
  funext x
  apply tsum_congr
  intro k
  simp [imageTerm, image, next, Polynomial.derivative_mul]
  ring

theorem kernel_deriv {s : ℝ} (hs : 0 < s) : deriv (GaussianChains.kernel s) = series .first s := by
  simpa only [Function.iterate_one] using (kernel_iterated_deriv hs 1).trans (series_first_eq s)

theorem kernel_secondDeriv {s : ℝ} (hs : 0 < s) : deriv (deriv (GaussianChains.kernel s)) =
    series .second s := by
  simpa [Function.iterate_succ_apply'] using (kernel_iterated_deriv hs 2).trans (series_second_eq s)

theorem hasDerivAt_series_value {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (series .value s) (series .first s x) x := by
  rw [series_value_eq_kernel, kernel_periodized, ← series_first_eq]
  exact periodized_derivative hs _ x

theorem hasDerivAt_series_first {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (series .first s) (series .second s x) x := by
  rw [← series_first_eq, ← series_second_eq]
  exact periodized_derivative hs _ x

def orderIndex : Order → ℕ
  | .value => 0
  | .first => 1
  | .second => 2

theorem iteratedDeriv_eq_series {s : ℝ} (hs : 0 < s) (j : Order) :
    deriv^[orderIndex j] (GaussianChains.kernel s) = series j s := by
  cases j with
  | value => exact (series_value_eq_kernel s).symm
  | first => exact kernel_deriv hs
  | second => exact kernel_secondDeriv hs

/-- The enclosure consumed by a certificate table applies to the true
iterated derivative of the kernel, including the two omitted half-lines. -/
theorem kernel_table_enclosure (j : Order) {s u x : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (has : (a:ℝ) ≤ s) (hsu : s ≤ u) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ℤ → ℚ)
    (h : ∀ k ∈ Finset.Icc (-3:ℤ) 3, image j s (x+k) ∈ Set.Icc (lo k:ℝ) (hi k:ℝ)) :
    let err := 4*(((2*u)^2*25+2*u)*(1/2:ℝ)^(9*a))
    (deriv^[orderIndex j] (GaussianChains.kernel s)) x ∈
      Set.Icc (((∑ k ∈ Finset.Icc (-3:ℤ) 3, lo k : ℚ):ℝ) - err)
        (((∑ k ∈ Finset.Icc (-3:ℤ) 3, hi k : ℚ):ℝ) + err) := by
  have hs : 0 < s := (Nat.cast_pos.mpr (by omega : 0 < a)).trans_le has
  rw [iteratedDeriv_eq_series hs]
  exact enclose_seven j ha has hsu hx lo hi h

#print axioms kernel_table_enclosure
#print axioms seven_image_error
#print axioms enclose_seven
#print axioms kernel_secondDeriv

end GaussianChains.ImageBounds

