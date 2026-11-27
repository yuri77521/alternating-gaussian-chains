import ChainGeometry
import ChainFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Sharp projection bound for sorted alternating charges. A phase projection is
an alternating sum of cosines. Its double is bounded by the total variation
of cos over the n full turns (also when some consecutive labels coincide). -/
noncomputable section
namespace GaussianChains.Strip
open Real MeasureTheory

private theorem integral_abs_sin_turns (a : ℝ) (n : ℕ) :
    (∫ t in a..a+(n:ℝ)*(2*π), |sin t|) = 4*(n:ℝ) := by
  have hp : Function.Periodic (fun t : ℝ => |sin t|) π := fun t => by simp
  have hbase : (∫ t in 0..π, |sin t|) = 2 := by
    rw [intervalIntegral.integral_congr (g:=Real.sin) (fun t ht => ?_), integral_sin]
    · norm_num
    · rw [Set.uIcc_of_le pi_pos.le] at ht
      exact abs_of_nonneg (sin_nonneg_of_mem_Icc ht)
  have h := hp.intervalIntegral_add_zsmul_eq (2*(n:ℤ)) a
    (fun _ _ => continuous_sin.abs.intervalIntegrable _ _)
  rw [hp.intervalIntegral_add_eq a 0, zero_add, hbase] at h
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat,Int.cast_natCast] at h
  rw [show (n:ℝ)*(2*π)=2*(n:ℝ)*π by ring,h]; ring

private theorem projected_variation (a : ℕ → ℝ) (n : ℕ)
    (hmono : ∀ k < 6, a k ≤ a (k+1)) (he : a 6 = a 0 +(n:ℝ)*(2*π)) :
    cos (a 0)-cos (a 1)+cos (a 2)-cos (a 3)+cos (a 4)-cos (a 5) ≤ 2*n := by
  let f (k : ℕ) := cos (a k)-cos (a (k+1))
  have hbound := Finset.sum_le_sum (s:=Finset.range 6)
    (f:=fun k => (-1:ℝ)^k*f k) (g:=fun k => ∫ z in a k..a (k+1), |sin z|)
    (fun k hk => show (-1:ℝ)^k*f k ≤ _ from calc
       _ ≤ |f k| := by
          rcases neg_one_pow_eq_or ℝ k with h|h <;> rw [h]
          · simpa using le_abs_self (f k)
          · simpa using neg_le_abs (f k)
       _ ≤ ∫ z in a k..a (k+1), |sin z| := by
          dsimp [f]; rw [← integral_sin]
          exact intervalIntegral.abs_integral_le_integral_abs (hmono k (Finset.mem_range.mp hk)))
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun _ _ =>
    continuous_sin.abs.intervalIntegrable _ _), he, integral_abs_sin_turns] at hbound
  have hcos : cos (a 6) = cos (a 0) := by rw [he,cos_add_nat_mul_two_pi]
  norm_num [Finset.sum_range_succ,f,hcos] at hbound
  linarith

/-- The bound holds for all modes on the full collision closure. -/
theorem structureFactor_le_two_mul {x : Fin 6 → ℝ} (hx : Feasible (by decide) 0 x) (n : ℕ) :
    ‖structureFactor x n‖ ≤ 2*n := by
  let z := structureFactor x n
  let rot := Complex.exp (-((z.arg : ℝ):ℂ)*Complex.I)
  have hrot : z*rot = (‖z‖:ℝ) := by
    calc
      z*rot = (((‖z‖ : ℝ):ℂ)*Complex.exp ((z.arg:ℂ)*Complex.I))*rot := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = _ := by dsimp [rot]; rw [mul_assoc,← Complex.exp_add]; simp
  let θ (k : ℕ) := 2*π*(n:ℝ)*liftSite (by decide) x k-z.arg
  have hm (k : ℕ) (_ : k < 6) : θ k ≤ θ (k+1) := by
    have h := hx ⟨k%6,Nat.mod_lt _ (by decide)⟩
    rw [← gap_lift_period] at h
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_nonneg.mp h) (by positivity)) _
  have he : θ 6 = θ 0+(n:ℝ)*(2*π) := by
    have h := liftSite_add_period (by decide : 0 < 6) x 0
    rw [Nat.zero_add] at h
    dsimp [θ]; rw [h]; ring
  have hvar := projected_variation θ n hm he
  have hre : (z*rot).re = ‖z‖ := by rw [hrot,Complex.ofReal_re]
  have hmode (i : Fin 6) :
      (Complex.exp (((2*π*(n:ℝ)*x i:ℝ):ℂ)*Complex.I)*rot).re = cos (θ i.val) := by
    dsimp only [rot,θ]
    rw [← Complex.exp_add,liftSite_fin,← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  have hproject : ‖z‖ = ∑ i : Fin 6, charge i*cos (θ i.val) := by
    rw [← hre]
    change ((∑ i : Fin 6, (charge i:ℂ)*Complex.exp (((2*π*(n:ℝ)*x i:ℝ):ℂ)*Complex.I))*rot).re = _
    rw [Finset.sum_mul,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc (charge i:ℂ),Complex.re_ofReal_mul,hmode]
  change ‖z‖ ≤ _
  rw [hproject]
  norm_num [Fin.sum_univ_succ,charge]
  linarith only [hvar]

/-- The complementary trivial estimate is better starting at mode four. -/
theorem structureFactor_le_six (x : Fin 6 → ℝ) (n : ℕ) : ‖structureFactor x n‖ ≤ 6 := by
  unfold structureFactor
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,Complex.norm_real,Real.norm_eq_abs]
  simp [charge,abs_pow]

end GaussianChains.Strip
