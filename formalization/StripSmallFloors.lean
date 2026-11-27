import ClustersWidth
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

/-! Infinite-frequency tail estimates in the small-floor part of Theorem 5. -/
noncomputable section
namespace GaussianChains.Strip

def tailTerm (p : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ((k+3:ℕ):ℝ)^p * q^((k+3)^2-1)

def highTail (p : ℕ) (q : ℝ) : ℝ := ∑' k, tailTerm p q k

def tailBound (p : ℕ) (r : ℝ) : ℝ :=
  3^p*r^8/(1-(4/3:ℝ)^p*r^7)

theorem highTail_le {p : ℕ} {q r : ℝ} (hq : 0 ≤ q) (hr : q ≤ r) (hr1 : r < 1)
    (hc : (4/3:ℝ)^p*r^7 < 1) : highTail p q ≤ tailBound p r := by
  have hr0 := hq.trans hr
  let R := (4/3:ℝ)^p*r^7
  have hsucc (k : ℕ) : tailTerm p q (k+1) ≤ tailTerm p q k*R := by
    have hn : ((k+1+3:ℕ):ℝ) ≤ ((k+3:ℕ):ℝ)*(4/3) := by
      push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hp := pow_le_pow_left₀ (by positivity) hn p
    rw [mul_pow] at hp
    have he : (k+1+3)^2 = (k+3)^2+(2*k+7) := by ring
    have hk : 0 < (k+3)^2 := by positivity
    have he' : (k+1+3)^2-1 = (k+3)^2-1+(2*k+7) := by omega
    have hq' := (pow_le_pow_of_le_one hq (hr.trans hr1.le) (show 7 ≤ 2*k+7 by omega)).trans
      (pow_le_pow_left₀ hq hr 7)
    unfold tailTerm
    rw [he',pow_add]
    calc
      _ ≤ (((k+3:ℕ):ℝ)^p*(4/3)^p)*(q^((k+3)^2-1)*r^7) :=
        mul_le_mul hp (mul_le_mul_of_nonneg_left hq' (pow_nonneg hq _)) (by positivity) (by positivity)
      _ = _ := by dsimp [R]; ring
  have hterm (k : ℕ) : tailTerm p q k ≤ (3^p*r^8)*R^k := by
    induction k with
    | zero =>
      simpa [tailTerm] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hr 8)
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) p)
    | succ k ih =>
      rw [pow_succ R k,← mul_assoc]
      exact (hsucc k).trans (mul_le_mul_of_nonneg_right ih (show 0 ≤ R by dsimp only [R]; positivity))
  have hgeo := (hasSum_geometric_of_lt_one (show 0 ≤ R by dsimp [R]; positivity) hc).mul_left (3^p*r^8)
  have hs : Summable (tailTerm p q) := Summable.of_nonneg_of_le
    (fun k => by unfold tailTerm; positivity) hterm hgeo.summable
  unfold highTail tailBound
  exact (hs.tsum_le_tsum hterm hgeo.summable).trans_eq (by rw [hgeo.tsum_eq]; rfl)

theorem widthR_split {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) :
    widthR q = 16*q^3 + highTail 4 q := by
  rw [widthR,(summable_widthTerm hq hq').tsum_eq_zero_add]
  change (2:ℝ)^4*q^3 + _ = _
  norm_num [highTail,tailTerm,widthTerm,add_assoc]

private theorem rexp_cap {s p v c : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hpi : v*p ≤ Real.pi^2) (hpos : 0 ≤ v) (n : ℕ)
    (hcert : 1 < c*∑ i ∈ Finset.range n, v^i/(i.factorial : ℝ)) (hc : 0 < c) :
    Real.exp (-(Real.pi^2)/s) < c := by
  have hl : v ≤ Real.pi^2/s :=
    (le_div_iff₀ hs).mpr ((mul_le_mul_of_nonneg_left hsp hpos).trans hpi)
  have he := (Real.sum_le_exp_of_nonneg hpos n).trans (Real.exp_le_exp.mpr hl)
  rw [neg_div,Real.exp_neg,inv_eq_one_div,div_lt_iff₀ (Real.exp_pos _)]
  exact hcert.trans_le (mul_le_mul_of_nonneg_left he hc.le)

theorem narrow_nome {s : ℝ} (hs : 0 < s) (h801 : s ≤ 801/100) :
    Real.exp (-(Real.pi^2)/s) < 292/1000 := by
  apply rexp_cap (p:=801/100) (v:=1232/1000) hs h801 _ (by norm_num) 9 _ (by norm_num)
  · nlinarith only [Real.pi_gt_d4,sq_nonneg (Real.pi-3.1415)]
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem broad_nome {s : ℝ} (hs : 0 < s) (h9 : s ≤ 9) :
    Real.exp (-(Real.pi^2)/s) < 335/1000 := by
  apply rexp_cap (p:=9) (v:=1095/1000) hs h9 _ (by norm_num) 8 _ (by norm_num)
  · nlinarith only [Real.pi_gt_d2,sq_nonneg (Real.pi-3.14)]
  · norm_num [Finset.sum_range_succ,Nat.factorial]

/-- All four columns in the two small-floor rows, with the actual infinite sums. -/
def TailCaps (q score slope curvature fourth : ℝ) : Prop :=
  16*q^3+4*highTail 2 q < score ∧ 16*q^3+10*highTail 2 q < slope ∧
  32*q^3+10*highTail 3 q < curvature ∧ widthR q < fourth

private theorem four_caps {q r a b c d : ℝ} (hq : 0 ≤ q) (hr : q ≤ r) (h1 : r < 1)
    (h2 : (4/3:ℝ)^2*r^7 < 1) (h3 : (4/3:ℝ)^3*r^7 < 1) (h4 : (4/3:ℝ)^4*r^7 < 1)
    (a' : 16*r^3+4*tailBound 2 r < a) (b' : 16*r^3+10*tailBound 2 r < b)
    (c' : 32*r^3+10*tailBound 3 r < c) (d' : 16*r^3+tailBound 4 r < d) :
    TailCaps q a b c d := by
  have hq3 := pow_le_pow_left₀ hq hr 3
  have ht2 := highTail_le hq hr h1 h2
  have ht3 := highTail_le hq hr h1 h3
  have ht4 := highTail_le hq hr h1 h4
  unfold TailCaps
  rw [widthR_split hq (lt_of_le_of_lt hr h1)]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem broad_tail_constants {s : ℝ} (hs : 8 ≤ s) (h9 : s ≤ 9) :
    TailCaps (Real.exp (-(Real.pi^2)/s)) (608/1000) (616/1000) (1246/1000) (615/1000) := by
  apply four_caps (r:=335/1000) (Real.exp_pos _).le (broad_nome (by linarith) h9).le <;>
    norm_num [tailBound]

theorem narrow_tail_constants {s : ℝ} (hs : 799/100 ≤ s) (h801 : s ≤ 801/100) :
    TailCaps (Real.exp (-(Real.pi^2)/s)) (405/1000) (41/100) (82/100) (41/100) := by
  apply four_caps (r:=292/1000) (Real.exp_pos _).le (narrow_nome (by linarith) h801).le <;>
    norm_num [tailBound]

end GaussianChains.Strip
