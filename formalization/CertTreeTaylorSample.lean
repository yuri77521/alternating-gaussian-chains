import CertTreeRanges
import CertTreeInterpolation

/-! The one-point score approximation used for trials and for box centers. -/
namespace GaussianChains.Cert.Tables
open Interval GaussianChains.Certificate

def midpoint (unit : ℕ+) (I : Interval) : ℚ := (⌊(I.lo+I.hi)/2*(unit:ℚ)⌋ : ℚ)/unit

def midpointOK (unit : ℕ+) (I : Interval) : Bool :=
  let m := midpoint unit I
  decide (m-2/unit ≤ I.lo ∧ I.hi ≤ m+2/unit)

theorem midpoint_error {I : Interval} {x : ℝ} {unit : ℕ+}
    (h : midpointOK unit I = true) (hx : I.Mem x) : |x-(midpoint unit I:ℝ)| ≤ 2/(unit:ℝ) := by
  have hh : midpoint unit I-2/(unit:ℚ) ≤ I.lo ∧ I.hi ≤ midpoint unit I+2/unit :=
    of_decide_eq_true h
  have hl : (midpoint unit I:ℝ)-2/(unit:ℝ) ≤ I.lo := by simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hh.1
  have hu : (I.hi:ℝ) ≤ midpoint unit I+2/(unit:ℝ) := by simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hh.2
  apply abs_le.mpr
  constructor <;> linarith [hx.1,hx.2]

def floorAt (unit : ℕ+) (a : ℚ) : ℚ := (⌊a*(unit:ℚ)⌋ : ℚ)/unit

theorem floorAt_error (unit : ℕ+) (a : ℚ) : |(a:ℝ) - (floorAt unit a:ℝ)| ≤ 1/(unit:ℝ) := by
  have hu : (0:ℚ) < unit := by exact_mod_cast unit.2
  have hlo : floorAt unit a ≤ a := (div_le_iff₀ hu).mpr (Int.floor_le _)
  have hhi : a - floorAt unit a ≤ 1/unit := by
    apply (le_div_iff₀ hu).mpr
    rw [sub_mul, floorAt, div_mul_cancel₀ _ hu.ne']
    linarith [Int.lt_floor_add_one (a*(unit:ℚ))]
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlo))]
  simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hhi

def taylorAt (M unit : ℕ+) (values slopes : ℕ → Interval) (q : ℚ) : ℚ :=
  let p := nearest M q
  midpoint unit (values p) +
    floorAt unit (midpoint unit (slopes p) * (q-(p:ℚ)/M))

def taylorBudget (M unit : ℕ+) (K : ℚ) : ℚ :=
  (4 + (⌈K*(unit:ℚ)/(8*(M:ℚ)^2)⌉:ℚ))/unit

theorem taylorAt_sound {f f' f'' : ℝ → ℝ} {K : ℚ} (hK : 0 ≤ K)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (bound : ∀ t, |f'' t| ≤ (K:ℝ)) (M unit : ℕ+) {values slopes : ℕ → Interval}
    {q : ℚ} (hq : q ∈ Set.Icc (0:ℚ) 1)
    (hv : (values (nearest M q)).Mem (f ((nearest M q:ℝ)/M)))
    (hs : (slopes (nearest M q)).Mem (f' ((nearest M q:ℝ)/M)))
    (hvOK : midpointOK unit (values (nearest M q)) = true)
    (hsOK : midpointOK unit (slopes (nearest M q)) = true) :
    |f (q:ℝ)-(taylorAt M unit values slopes q:ℝ)| ≤ (taylorBudget M unit K:ℝ) := by
  let a : ℝ := (nearest M q:ℝ)/M
  let v : ℝ := midpoint unit (values (nearest M q))
  let p : ℝ := midpoint unit (slopes (nearest M q))
  have h := taylor_sample_error (D:=Set.univ) (M:=(K:ℝ)) (a:=a) (x:=(q:ℝ)) (v:=v) (p:=p)
    convex_univ (fun t _ => hf t) (fun t _ => hf' t) (fun t _ => bound t)
    (Set.mem_univ _) (Set.mem_univ _) (midpoint_error hvOK hv) (midpoint_error hsOK hs)
  have hδ := (nearest_bound (M:=M) (x:=(q:ℝ)) (by exact_mod_cast hq.1) (by exact_mod_cast hq.2)).2
  rw [nearest_cast] at hδ
  change |(q:ℝ)-a| ≤ _ at hδ
  have hM : (0:ℝ) < M := by exact_mod_cast M.2
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ (M:ℕ) from M.2)
  have hU : (0:ℝ) < unit := by exact_mod_cast unit.2
  have hsquare : ((q:ℝ)-a)^2 ≤ (1/(2*(M:ℝ)))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have hδ₂ : |(q:ℝ)-a| ≤ 1/2 := hδ.trans ((div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith))
  have h₁ : (K:ℝ)*((q:ℝ)-a)^2/2 ≤ (K:ℝ)/(8*(M:ℝ)^2) := by
    calc _ ≤ (K:ℝ)*(1/(2*(M:ℝ)))^2/2 := by exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by exact_mod_cast hK)) (by norm_num)
         _ = _ := by ring
  have h₂ : (2/(unit:ℝ))*|(q:ℝ)-a| ≤ 1/(unit:ℝ) := by
    calc _ ≤ (2/(unit:ℝ))*(1/2) := mul_le_mul_of_nonneg_left hδ₂ (by positivity)
         _ = _ := by ring
  let delta : ℚ := midpoint unit (slopes (nearest M q)) * (q-(nearest M q:ℚ)/M)
  have hflo := floorAt_error unit delta
  have heq : ((v+p*((q:ℝ)-a))-(taylorAt M unit values slopes q:ℝ)) =
      (delta:ℝ)-(floorAt unit delta:ℝ) := by
    dsimp [taylorAt, a, v, p, delta]; push_cast; ring
  have htotal := abs_sub_le (f (q:ℝ)) (v+p*((q:ℝ)-a)) (taylorAt M unit values slopes q:ℝ)
  rw [heq] at htotal
  have hceil : (K:ℝ)*(unit:ℝ)/(8*(M:ℝ)^2) ≤ (⌈K*(unit:ℚ)/(8*(M:ℚ)^2)⌉:ℤ) := by
    have ht := (Rat.cast_le (K:=ℝ)).mpr (Int.le_ceil (K*(unit:ℚ)/(8*(M:ℚ)^(2:ℕ))))
    simpa only [Rat.cast_intCast, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using ht
  have hbudget : (K:ℝ)/(8*(M:ℝ)^2) + 4/(unit:ℝ) ≤ (taylorBudget M unit K:ℝ) := by
    have hh : (K:ℝ)/(8*(M:ℝ)^2) ≤ (⌈K*(unit:ℚ)/(8*(M:ℚ)^2)⌉:ℤ)/(unit:ℝ) := by
      apply (le_div_iff₀ hU).mpr
      convert hceil using 1 <;> ring
    calc _ ≤ (⌈K*(unit:ℚ)/(8*(M:ℚ)^2)⌉:ℤ)/(unit:ℝ) + 4/(unit:ℝ) := add_le_add hh le_rfl
         _ = _ := by unfold taylorBudget; push_cast; ring
  apply le_trans _ hbudget
  calc _ ≤ _ := htotal.trans (add_le_add h hflo)
       _ ≤ (K:ℝ)/(8*(M:ℝ)^2) + 2/(unit:ℝ) + 1/(unit:ℝ) + 1/(unit:ℝ) :=
         add_le_add (add_le_add (add_le_add h₁ le_rfl) h₂) le_rfl
       _ = _ := by ring

end GaussianChains.Cert.Tables
