import BandLeaves
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact rational arithmetic for the centered value leaf of the frozen strip search. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Finset Interval

abbrev Center := Fin 6 → ℚ
def liftCenter (c : Center) (i : Fin 6) : ℝ := c i
def arcMass (c : Center) (p : Pair) : ℚ := ∑ k ∈ arc p.1 p.2, c k
def distQ (h : ℚ) (c : Center) (p : Pair) : ℚ :=
  (p.2.val-p.1.val : ℕ)*h + (1-6*h)*arcMass c p
def middle (floor : Interval) : ℚ := (floor.lo+floor.hi)/2

def pairSlope (q : Oracle) (floor : Interval) (B : Box 6) (p : Pair) : Interval :=
  (singleton (coefficient p)).mul (q 1 (pairRange floor B p.1 p.2))

def hSlopeBounds (q : Oracle) (floor : Interval) (B : Box 6) (c : Center) : Interval :=
  sumRange pairs fun p => (pairSlope q floor B p).mul
    (singleton (((p.2.val-p.1.val : ℕ) : ℚ) - 6*arcMass c p))

def cutBounds (q : Oracle) (floor : Interval) (B : Box 6) (k : Fin 6) : Interval :=
  sumRange (pairs.filter fun p => k ∈ arc p.1 p.2) (pairSlope q floor B)

def centerApprox (sample : ℚ → ℚ) (floor : Interval) (c : Center) : ℚ :=
  ∑ p ∈ pairs, coefficient p * sample (distQ (middle floor) c p)

def floorError (q : Oracle) (floor : Interval) (B : Box 6) (c : Center) : ℚ :=
  let I := hSlopeBounds q floor B c
  max |I.lo| |I.hi| * ((floor.hi-floor.lo)/2)

def shiftGain (q : Oracle) (floor : Interval) (B : Box 6) (c : Center) : ℚ :=
  (1-6*floor.lo) * ∑ k,
    let g := cutBounds q floor B k
    max (max (((B k).hi-c k)*g.hi) (((B k).lo-c k)*g.lo)) 0

def validCenter (B : Box 6) (c : Center) : Bool :=
  decide ((∀ i, 0 ≤ c i ∧ (B i).lo ≤ c i ∧ c i ≤ (B i).hi) ∧ ∑ i, c i = 1)

def accurateCenter (ok : ℚ → Bool) (floor : Interval) (c : Center) : Bool :=
  decide (∀ p ∈ pairs, ok (distQ (middle floor) c p) = true)

def fitFloor (I : Interval) : Bool := decide (0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.hi ≤ 1/6)

def centerRadius (q : Oracle) (eps : ℚ) (floor : Interval) (B : Box 6) (c : Center) : ℚ :=
  pairs.card * eps + floorError q floor B c

def valueTest (q : Oracle) (sample : ℚ → ℚ) (eps : ℚ) (ok : ℚ → Bool)
    (floor : Interval) (B : Box 6) (c : Center) (j : Fin 5) : Bool :=
  fitFloor floor && validCenter B c && accurateCenter ok floor c && accurateCenter ok floor (trial j) &&
    decide (centerApprox sample floor c + centerRadius q eps floor B c + shiftGain q floor B c <
      centerApprox sample floor (trial j) - centerRadius q eps floor (trialBox j) (trial j))

theorem cast_distQ (h : ℚ) (c : Center) (p : Pair) :
    (distQ h c p : ℝ) = distance h (liftCenter c) p := by
  simp [distQ, distance, arcMass, liftCenter]

theorem validCenter_sound {B : Box 6} {c : Center} (hc : validCenter B c = true) :
    B.Mem (liftCenter c) ∧ simplex (liftCenter c) := by
  have H := of_decide_eq_true hc
  constructor
  · intro i
    change ((B i).lo : ℝ) ≤ (c i : ℝ) ∧ (c i : ℝ) ≤ ((B i).hi : ℝ)
    exact ⟨by exact_mod_cast (H.1 i).2.1, by exact_mod_cast (H.1 i).2.2⟩
  · constructor
    · intro i
      change (0 : ℝ) ≤ (c i : ℝ)
      exact_mod_cast (H.1 i).1
    · change (∑ i, (c i : ℝ)) = 1
      exact_mod_cast H.2

theorem floor_data {I : Interval} (hf : fitFloor I = true) :
    0 ≤ (I.lo : ℝ) ∧ (I.lo:ℝ) ≤ (I.hi:ℝ) ∧ (I.hi:ℝ) ≤ 1/6 := by
  have H := of_decide_eq_true hf
  have hu : (I.hi:ℝ) ≤ ((1/6:ℚ):ℝ) := Rat.cast_le.mpr H.2.2
  exact ⟨by exact_mod_cast H.1, by exact_mod_cast H.2.1, by simpa using hu⟩

theorem middle_mem {I : Interval} (hf : fitFloor I = true) : I.Mem (middle I : ℝ) := by
  have H := (floor_data hf).2.1
  unfold middle
  push_cast
  constructor <;> linarith

def FirstOracleSound (q : Oracle) (F : ℕ → ℝ → ℝ) : Prop :=
  ∀ (I : Interval) (x : ℝ), I.Mem x → 0 ≤ x → x ≤ 1 → (q 1 I).Mem (F 1 x)

theorem pairSlope_sound {q : Oracle} {F : ℕ → ℝ → ℝ} (hq : FirstOracleSound q F)
    {floor : Interval} {B : Box 6} {h : ℝ} {u : Fin 6 → ℝ} (hf : fitFloor floor = true)
    (hh : floor.Mem h) (hb : B.Mem u) (hs : simplex u) (p : Pair) :
    (pairSlope q floor B p).Mem ((coefficient p : ℝ) * F 1 (distance h u p)) := by
  have H := floor_data hf
  have hu := distance_unit (H.1.trans hh.1) (hh.2.trans H.2.2) hs p
  exact mul_mem (singleton_mem _) (hq _ _ (pairRange_mem hh hb hs.2 p.1 p.2) hu.1 hu.2)

theorem value_eq_sum (F : ℕ → ℝ → ℝ) (h : ℝ) (u : Fin 6 → ℝ) :
    expression .value F h u = ∑ p ∈ pairs, (coefficient p : ℝ)*F 0 (distance h u p) := by
  simp [expression, weight, order]

/-- Linear segment, in either floor or slack coordinates. -/
def mix (a b t : ℝ) : ℝ := (1-t)*a+t*b

theorem mix_mem {I : Interval} {a b t : ℝ} (ha : I.Mem a) (hb : I.Mem b)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : I.Mem (mix a b t) := by
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  unfold mix
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left ha.1 ht', mul_le_mul_of_nonneg_left hb.1 ht.1]
  · nlinarith only [mul_le_mul_of_nonneg_left ha.2 ht', mul_le_mul_of_nonneg_left hb.2 ht.1]

theorem mixed_simplex {u v : Fin 6 → ℝ} (hu : simplex u) (hv : simplex v)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    simplex (fun i => mix (u i) (v i) t) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hu.1 i)) (mul_nonneg ht.1 (hv.1 i))
  · simp [mix, sum_add_distrib, ← mul_sum, hu.2, hv.2]

theorem mix_deriv (a b t : ℝ) : HasDerivAt (mix a b) (b-a) t := by
  convert (((hasDerivAt_id t).const_sub (1:ℝ)).mul_const a).add ((hasDerivAt_id t).mul_const b)
    using 1 <;> simp [mix] <;> ring

theorem unit_mvt {f D : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (D t) t) :
    ∃ t ∈ Set.Ioo (0:ℝ) 1, f 1-f 0 = D t := by
  obtain ⟨t,ht,h⟩ := exists_hasDerivAt_eq_slope f D zero_lt_one
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  exact ⟨t,ht,by simpa using h.symm⟩

theorem sum_deriv {F : ℕ → ℝ → ℝ} (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x)
    {d : ℝ → Pair → ℝ} {D : Pair → ℝ} {t : ℝ}
    (hd : ∀ p ∈ pairs, HasDerivAt (fun w => d w p) (D p) t) :
    HasDerivAt (fun w => ∑ p ∈ pairs, (coefficient p : ℝ)*F 0 (d w p))
      (∑ p ∈ pairs, (coefficient p : ℝ)* (F 1 (d t p)*D p)) t := by
  exact HasDerivAt.fun_sum fun p hp =>
    ((hF (d t p)).comp t (hd p hp)).const_mul (coefficient p : ℝ)

end GaussianChains.Band

