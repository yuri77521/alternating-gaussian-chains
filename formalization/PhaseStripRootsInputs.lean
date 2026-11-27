import CertTree
import CertRootExp
import ClusterSeriesCosine
import Mathlib.Analysis.Real.Pi.Bounds

/-! Outward enclosures of the two transcendental inputs for the endpoint
slopes in Table 2. The cosine uses a reduced angle and twenty double angles. -/
namespace GaussianChains.PhaseStrip

open GaussianChains.Cert

def piLo : ℚ := 3.14159265358979323846
def piHi : ℚ := 3.14159265358979323847

private theorem pi_bounds : (piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piHi : ℝ) := by
  constructor
  · exact Real.pi_gt_d20.le
  · exact Real.pi_lt_d20.le

/-- The Gaussian nome at a rational strip width. -/
def qInput (s : ℚ) : Interval :=
  let I := CertExp.negExpRange (piLo^2/s) (piHi^2/s)
  ⟨I.1,I.2⟩

theorem qInput_mem {s : ℚ} (hs : 8 ≤ s) (_hs' : s ≤ 9) :
    (qInput s).Mem (Real.exp (-(Real.pi^2)/(s:ℝ))) := by
  have hs0 : 0 < s := by linarith
  have hsR : (0:ℝ) < s := by exact_mod_cast hs0
  have hlo := pow_le_pow_left₀ (show (0:ℝ) ≤ piLo by norm_num [piLo]) pi_bounds.1 2
  have hhi := pow_le_pow_left₀ Real.pi_pos.le pi_bounds.2 2
  have h := CertExp.negExpRange_sound (lo := piLo^2/s) (hi := piHi^2/s)
    (x := Real.pi^2/(s:ℝ)) (by positivity)
    (by rw [div_le_iff₀ hs0]; linarith [show piHi^2 ≤ 10 by norm_num [piHi]])
    (by push_cast; exact div_le_div_of_nonneg_right hlo hsR.le)
    (by push_cast; exact div_le_div_of_nonneg_right hhi hsR.le)
  simpa only [neg_div] using h

private def grid : ℚ := 2^200
private def down (v : ℚ) : ℚ := (⌊v*grid⌋ : ℚ)/grid
private def up (v : ℚ) : ℚ := (⌈v*grid⌉ : ℚ)/grid
private theorem down_le (v : ℚ) : down v ≤ v :=
  (div_le_iff₀ (by norm_num [grid] : 0<grid)).mpr (Int.floor_le _)
private theorem le_up (v : ℚ) : v ≤ up v :=
  (le_div_iff₀ (by norm_num [grid] : 0<grid)).mpr (Int.le_ceil _)

private def doubleLo (v : ℚ) := down (2*(max 0 v)^2-1)
private def doubleHi (v : ℚ) := up (2*(max 0 v)^2-1)

private theorem double_sound {lo hi : ℚ} {a : ℝ} (ha : 0 ≤ Real.cos a)
    (hl : (lo : ℝ) ≤ Real.cos a) (hu : Real.cos a ≤ (hi : ℝ)) :
    (doubleLo lo : ℝ) ≤ Real.cos (2*a) ∧ Real.cos (2*a) ≤ (doubleHi hi : ℝ) := by
  rw [Real.cos_two_mul]
  have h₁ : (doubleLo lo : ℝ) ≤ ((2*(max 0 lo)^2-1 : ℚ):ℝ) :=
    Rat.cast_le.mpr (down_le _)
  have h₂ : ((2*(max 0 hi)^2-1 : ℚ):ℝ) ≤ (doubleHi hi : ℝ) :=
    Rat.cast_le.mpr (le_up _)
  change ((down _ : ℚ):ℝ) ≤ _ ∧ _ ≤ ((up _ : ℚ):ℝ)
  apply And.intro (h₁.trans _) (le_trans _ h₂)
  · push_cast
    nlinarith [pow_le_pow_left₀ (le_max_left (0:ℝ) lo) (max_le ha hl) 2]
  · push_cast
    nlinarith [pow_le_pow_left₀ ha (hu.trans (le_max_right (0:ℝ) hi)) 2]

private def doubles (f : ℚ → ℚ) : ℕ → ℚ → ℚ
  | 0,v => v
  | k+1,v => doubles f k (f v)

private theorem doubles_sound (k : ℕ) {lo hi : ℚ} {a : ℝ}
    (ha : 0 ≤ a) (ha' : 2^k*a ≤ Real.pi/2)
    (hl : (lo:ℝ) ≤ Real.cos a) (hu : Real.cos a ≤ (hi:ℝ)) :
    (doubles doubleLo k lo : ℝ) ≤ Real.cos (2^k*a) ∧
      Real.cos (2^k*a) ≤ (doubles doubleHi k hi : ℝ) := by
  induction k generalizing a lo hi with
  | zero => simpa [doubles] using And.intro hl hu
  | succ k ih =>
    have hscale : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    have hcos : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by
      nlinarith [mul_le_mul_of_nonneg_right hscale ha]⟩
    have hstep := double_sound hcos hl hu
    have harg : (2:ℝ)^k*(2*a) = 2^(k+1)*a := by rw [pow_succ]; ring
    simpa only [doubles,harg] using ih (a:=2*a) (by positivity) (harg ▸ ha') hstep.1 hstep.2

private def size : ℚ := 2^20
private def aLo (h : ℚ) := 2*piLo*h/size
private def aHi (h : ℚ) := 2*piHi*h/size
private def startLo (h : ℚ) :=
  down (1-(aHi h)^2/2+(aLo h)^4/24-(aHi h)^6/720)
private def startHi (h : ℚ) :=
  up (1-(aLo h)^2/2+(aHi h)^4/24+(aHi h)^6/720)

def xInput (h : ℚ) : Interval :=
  ⟨doubles doubleLo 20 (startLo h),doubles doubleHi 20 (startHi h)⟩

theorem xInput_mem {h : ℚ} (hh : 1/8 ≤ h) (hh' : h ≤ 1/6) :
    (xInput h).Mem (Real.cos (2*Real.pi*(h:ℝ))) := by
  let a := 2*Real.pi*(h:ℝ)/(2^20)
  have hh0 : (0:ℝ) ≤ h := by exact_mod_cast (by linarith : (0:ℚ) ≤ h)
  have hhU : (h:ℝ) ≤ 1/6 := by simpa using (Rat.cast_le.mpr hh' : (h:ℝ) ≤ ((1/6:ℚ):ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha₀ : (0:ℝ) ≤ (aLo h:ℝ) := by
    unfold aLo size piLo
    push_cast
    positivity
  have hlow : (aLo h:ℝ) ≤ a := by
    unfold aLo size a
    push_cast
    gcongr
    exact pi_bounds.1
  have hupp : a ≤ (aHi h:ℝ) := by
    unfold aHi size a
    push_cast
    gcongr
    exact pi_bounds.2
  have hlo := fun j : ℕ => pow_le_pow_left₀ ha₀ hlow j
  have hhi := fun j : ℕ => pow_le_pow_left₀ ha hupp j
  obtain ⟨hl,hu⟩ := abs_le.mp (ClusterSeries.cos_fourth_bound a)
  have sLo : (startLo h:ℝ) ≤ Real.cos a := by
    apply (Rat.cast_le.mpr (down_le _)).trans
    push_cast
    linarith [hlo 4,hhi 2,hhi 6]
  have sHi : Real.cos a ≤ (startHi h:ℝ) := by
    apply le_trans _ (Rat.cast_le.mpr (le_up _))
    push_cast
    linarith [hlo 2,hhi 4,hhi 6]
  have hend : (2:ℝ)^20*a = 2*Real.pi*(h:ℝ) := by dsimp [a]; ring
  have ha' : (2:ℝ)^20*a ≤ Real.pi/2 := by
    rw [hend]
    nlinarith [mul_le_mul_of_nonneg_left hhU Real.pi_pos.le,Real.pi_pos]
  simpa only [Interval.Mem,xInput,hend] using doubles_sound 20 ha ha' sLo sHi

end GaussianChains.PhaseStrip
