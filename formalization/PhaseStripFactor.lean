import PhaseStripFinite
import PhaseStripTails
import PhaseStripDerivative

namespace GaussianChains.PhaseStrip

open Cert GaussianChains.PackedFace Real Set

def widen (I : Interval) (r : ℚ) : Interval := ⟨I.lo-r,I.hi+r⟩
theorem widen_mem {I : Interval} {r : ℚ} {x y : ℝ} (hy : I.Mem y)
    (he : |x-y| < (r:ℝ)) : (widen I r).Mem x := by
  obtain ⟨hl,hu⟩ := abs_lt.mp he
  rcases hy with ⟨ha,hb⟩
  unfold widen Interval.Mem
  push_cast
  constructor <;> linarith

def reciprocal (I : Interval) : Interval := ⟨1/I.hi,1/I.lo⟩

theorem reciprocal_mem {I : Interval} {x : ℝ} (hx : I.Mem x) (h : 0 < I.lo) :
    (reciprocal I).Mem (1/x) := by
  have h₁ : (0:ℝ) < I.lo := by exact_mod_cast h
  simpa [reciprocal, Interval.Mem] using And.intro
    (one_div_le_one_div_of_le (h₁.trans_le hx.1) hx.2)
    (one_div_le_one_div_of_le h₁ hx.1)

def checkSine (X Y : Interval) : Prop :=
  0 ≤ X.lo ∧ 0 ≤ Y.lo ∧ 0 ≤ Y.hi ∧ Y.lo^2 ≤ 1-X.hi^2 ∧ 1-X.lo^2 ≤ Y.hi^2
instance (X Y : Interval) : Decidable (checkSine X Y) := by unfold checkSine; infer_instance

theorem sqrt_mem {X Y : Interval} {x : ℝ} (hX : X.Mem x) (h : checkSine X Y) :
    Y.Mem (sqrt (1-x^2)) := by
  obtain ⟨hx,hy,hy',ha,hb⟩ := h
  have hx' : (0:ℝ) ≤ X.lo := by exact_mod_cast hx
  have h₁ := pow_le_pow_left₀ (hx'.trans hX.1) hX.2 2
  have h₂ := pow_le_pow_left₀ hx' hX.1 2
  have h₃ : (Y.lo:ℝ)^2 ≤ 1-(X.hi:ℝ)^2 := by exact_mod_cast ha
  have h₄ : 1-(X.lo:ℝ)^2 ≤ (Y.hi:ℝ)^2 := by exact_mod_cast hb
  have h₆ : (0:ℝ) ≤ Y.hi := by exact_mod_cast hy'
  exact ⟨le_sqrt_of_sq_le (by linarith), sqrt_le_iff.mpr ⟨h₆,by linarith⟩⟩

def dxBox (b : Bool) (Q X : Interval) := widen (sixBox .dx b Q X) (4/10^18)
def qdqBox (b : Bool) (Q X : Interval) := widen (sixBox .qdq b Q X) (8/10^19)
def denomBox (b : Bool) (Q X Y : Interval) := Y.mul (dxBox b Q X)
def factorBox (b : Bool) (Q X Y : Interval) :=
  (qdqBox b Q X).mul (reciprocal (denomBox b Q X Y))

theorem factorBox_mem (b : Bool) {q x : ℝ} {Q X Y : Interval}
    (hq : 0 ≤ q) (hmax : q ≤ faceQ) (hx : x ∈ Icc (1/2) (sqrt 2/2))
    (hQ : Q.Mem q) (hX : X.Mem x) (hY : checkSine X Y)
    (hpos : 0 < (denomBox b Q X Y).lo) : (factorBox b Q X Y).Mem (phaseFactor b q x) := by
  have ⟨hu,hz⟩ := z_range b hx
  have hd := (z_path b hx).2
  have hxp : (dxBox b Q X).Mem
      (∑' k : ℕ, endpointDx (k+1) q x (endpointZ b x) (endpointZ' b x)) := by
    apply widen_mem (sixBox_mem .dx b hQ hX)
    simpa only [summand, zAt, dzAt, endpointZ, endpointZ', Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using dx_six_error hq hmax hu hz hd
  have hqp : (qdqBox b Q X).Mem
      (q * ∑' k : ℕ, endpointDq (k+1) q x (endpointZ b x)) := by
    apply widen_mem (sixBox_mem .qdq b hQ hX)
    simpa only [summand, zAt, endpointZ, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      scaled_dq_six_error hq hmax hu hz
  have hy := sqrt_mem hX hY
  simpa [phaseFactor, factorBox, div_eq_mul_inv] using
    Interval.mul_mem hqp (reciprocal_mem (Interval.mul_mem hy hxp) hpos)

end GaussianChains.PhaseStrip

