import BifurcationJetDefs
import CertRootExp
import CertTree

/-! Kernel-checked intervals for the centered pitchfork at width eight. -/

namespace GaussianChains.Bifurcation.Images
open GaussianChains.Cert GaussianChains.CertExp
open Interval
open scoped BigOperators

private def C := Interval.singleton

private def sc (a : ℚ) (I : Interval) := (C a).mul I
private def sub (I J : Interval) := I.add J.neg

private theorem c_mem (a : ℚ) : (C a).Mem (a:ℝ) := singleton_mem a

private theorem sc_mem {I : Interval} {x : ℝ} (a : ℚ) (H : I.Mem x) :
    (sc a I).Mem ((a:ℝ)*x) := mul_mem (c_mem _) H

private theorem sub_mem {I J : Interval} {x y : ℝ} (H : I.Mem x) (K : J.Mem y) :
    (sub I J).Mem (x-y) := by simpa only [sub_eq_add_neg] using add_mem H (neg_mem K)

private def power (I : Interval) : ℕ → Interval
  | 0 => C 1
  | n+1 => (power I n).mul I

private theorem power_mem {I : Interval} {x : ℝ} (H : I.Mem x) (n : ℕ) :
    (power I n).Mem (x^n) := by
  induction n with
  | zero => simpa [power] using (c_mem 1)
  | succ n ih => exact pow_succ x n ▸ mul_mem ih H

private def expNeg (I : Interval) : Interval :=
  if 0 ≤ I.hi ∧ I.hi ≤ 600 ∧ I.lo ≤ I.hi then
    ⟨(negExpBox I.hi).1, (negExpBox (max 0 I.lo)).2⟩
  else ⟨0,1⟩

private theorem expNeg_mem {I : Interval} {x : ℝ} (H : I.Mem x) (hx : 0 ≤ x) :
    (expNeg I).Mem (Real.exp (-x)) := by
  unfold expNeg
  split_ifs with HQ
  · obtain ⟨a,b,c⟩ := HQ
    have hL := (negExpBox_sound a b).1
    have hU := (negExpBox_sound (le_max_left 0 I.lo)
      (max_le (by norm_num) (c.trans b))).2
    refine ⟨hL.trans (Real.exp_le_exp.mpr (neg_le_neg H.2)), ?_⟩
    apply le_trans (Real.exp_le_exp.mpr (neg_le_neg ?_)) hU
    push_cast
    exact max_le hx H.1
  · exact ⟨by simpa using (Real.exp_pos (-x)).le, by simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)⟩

private def polyBox (o : Order) (I : Interval) : Interval :=
  match o with
  | .value => C 1
  | .first => sc (-16) I
  | .second => sub (sc 256 (power I 2)) (C 16)
  | .third => sub (sc 768 I) (sc 4096 (power I 3))
  | .fourth => (sub (sc 65536 (power I 4)) (sc 24576 (power I 2))).add (C 768)

private theorem poly_mem (o : Order) {I : Interval} {x : ℝ} (H : I.Mem x) :
    (polyBox o I).Mem (polynomial o x) := by
  cases o
  · simpa [polyBox,polynomial] using c_mem 1
  · simpa [polyBox,polynomial] using sc_mem (-16) H
  · simpa [polyBox,polynomial] using sub_mem (sc_mem 256 (power_mem H 2)) (c_mem 16)
  · simpa [polyBox,polynomial] using sub_mem (sc_mem 768 H) (sc_mem 4096 (power_mem H 3))
  · simpa [polyBox,polynomial] using add_mem
      (sub_mem (sc_mem 65536 (power_mem H 4)) (sc_mem 24576 (power_mem H 2))) (c_mem 768)

private def termBox (o : Order) (I : Interval) (k : ℤ) : Interval :=
  let J := I.add (C k)
  (polyBox o J).mul (expNeg (sc 8 (power J 2)))

private theorem termBox_mem (o : Order) {I : Interval} {x : ℝ} (H : I.Mem x) (k : ℤ) :
    (termBox o I k).Mem (term o x k) := by
  have HJ : (I.add (C k)).Mem (x+(k:ℝ)) := by simpa using add_mem H (c_mem k)
  have HH := sc_mem 8 (power_mem HJ 2)
  push_cast at HH
  simpa [termBox,term,neg_mul] using mul_mem (poly_mem o HJ) (expNeg_mem HH (by positivity))

def imageBox (o : Order) (I : Interval) : Interval :=
  ⟨(∑ k ∈ Finset.Icc (-4:ℤ) 4, (termBox o I k).lo)-radius,
   (∑ k ∈ Finset.Icc (-4:ℤ) 4, (termBox o I k).hi)+radius⟩

theorem imageBox_mem (o : Order) {I : Interval} {x : ℝ} (hx : |x| ≤ 1)
    (H : I.Mem x) : (imageBox o I).Mem (kernelD o x) := by
  have hi := Finset.sum_le_sum (s := Finset.Icc (-4:ℤ) 4) (fun k _ => (termBox_mem o H k).2)
  have lo := Finset.sum_le_sum (s := Finset.Icc (-4:ℤ) 4) (fun k _ => (termBox_mem o H k).1)
  have he := abs_le.mp (finite_error o hx)
  unfold imageBox Interval.Mem
  push_cast
  constructor <;> linarith [he.1,he.2]

def lowerFloor : ℚ := 13114680495074/100000000000000
def upperFloor : ℚ := 13114680495076/100000000000000
def rootBand : Interval := ⟨lowerFloor,upperFloor⟩

private def curvBox (o : Order) (H : Interval) :=
  sc (1/3) ((sub (sc 3 (imageBox o (C (1/2)))) (sc 4 (imageBox o ((C (1/2)).add H)))).add
      (sc 2 (imageBox o ((C (1/2)).add (sc 2 H)))))

private def mixBox (H : Interval) :=
  sc (1/3) ((sc (-4) (imageBox .third ((C (1/2)).add H))).add
    (sc 4 (imageBox .third ((C (1/2)).add (sc 2 H)))))

private def inwardBox (H : Interval) :=
  sc (1/3) (sub ((sub (imageBox .first H) (imageBox .first (sc 2 H))).add
    (imageBox .first (sub (C (1/2)) H))) (imageBox .first (sub (C (1/2)) (sc 2 H))))

private theorem boxes_sound {h : ℝ} {I : Interval} (hh : I.Mem h) (h₀ : 0 ≤ h) (h₁ : h ≤ 1/6) :
    (∀ o, (curvBox o I).Mem (curvatureAt o h)) ∧
    (mixBox I).Mem (mixedAt h) ∧ (inwardBox I).Mem (inwardAt h) := by
  have A : (C (1/2)).Mem (1/2:ℝ) := by simpa using c_mem (1/2)
  have B : (sc 2 I).Mem (2*h) := by simpa using sc_mem 2 hh
  have p (o : Order) {x : ℝ} {J : Interval} (hj : J.Mem x) (h1 : -1 ≤ x) (h2 : x ≤ 1) :=
    imageBox_mem o (abs_le.mpr ⟨h1,h2⟩) hj
  refine ⟨fun o => ?_,?_,?_⟩
  · have H := sc_mem (1/3) (add_mem (sub_mem
        (sc_mem 3 (p o A (by norm_num) (by norm_num)))
        (sc_mem 4 (p o (add_mem A hh) (by linarith) (by linarith))))
      (sc_mem 2 (p o (add_mem A B) (by linarith) (by linarith))))
    unfold curvBox curvatureAt
    convert H using 1 <;> push_cast <;> ring
  · have H := sc_mem (1/3) (add_mem
        (sc_mem (-4) (p .third (add_mem A hh) (by linarith) (by linarith)))
        (sc_mem 4 (p .third (add_mem A B) (by linarith) (by linarith))))
    unfold mixBox mixedAt
    convert H using 1 <;> push_cast <;> ring
  · have H := sc_mem (1/3) (sub_mem
        (add_mem (sub_mem (p .first hh (by linarith) (by linarith))
          (p .first B (by linarith) (by linarith)))
          (p .first (sub_mem A hh) (by linarith) (by linarith)))
        (p .first (sub_mem A B) (by linarith) (by linarith)))
    unfold inwardBox inwardAt
    convert H using 1 <;> push_cast <;> ring

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem decision :
    (0 < (curvBox .second (C lowerFloor)).lo ∧ (curvBox .second (C upperFloor)).hi < 0) ∧
    (-58.94248 < (mixBox rootBand).lo ∧ (mixBox rootBand).hi < -58.94246) ∧
    (70.22242 < (curvBox .fourth rootBand).lo ∧ (curvBox .fourth rootBand).hi < 70.22244) ∧
    (0.40191212 < (inwardBox rootBand).lo ∧ (inwardBox rootBand).hi < 0.40191214) := by
  decide +kernel

theorem root_endpoint_signs :
    0 < curvatureAt .second (lowerFloor : ℝ) ∧ curvatureAt .second (upperFloor : ℝ) < 0 := by
  have L := (boxes_sound (c_mem lowerFloor) (by norm_num [lowerFloor]) (by norm_num [lowerFloor])).1 .second
  have U := (boxes_sound (c_mem upperFloor) (by norm_num [upperFloor]) (by norm_num [upperFloor])).1 .second
  exact ⟨(by exact_mod_cast decision.1.1 : (0:ℝ) < _).trans_le L.1,
    U.2.trans_lt (by exact_mod_cast decision.1.2)⟩

theorem coefficients_on_rootBand {h : ℝ} (hh : rootBand.Mem h) :
    (-58.94248 < mixedAt h ∧ mixedAt h < -58.94246) ∧
    (70.22242 < curvatureAt .fourth h ∧ curvatureAt .fourth h < 70.22244) ∧
    (0.40191212 < inwardAt h ∧ inwardAt h < 0.40191214) := by
  have ha := hh.1
  have hb := hh.2
  norm_num [rootBand,lowerFloor,upperFloor] at ha hb
  obtain ⟨H,M,R⟩ := boxes_sound hh (by linarith) (by linarith)
  have lift {l u : ℚ} {x : ℝ} {I : Interval} (hi : I.Mem x)
      (hl : l < I.lo) (hu : I.hi < u) : (l:ℝ)<x ∧ x<(u:ℝ) :=
    ⟨(Rat.cast_lt.mpr hl).trans_le hi.1,hi.2.trans_lt (Rat.cast_lt.mpr hu)⟩
  obtain ⟨_,a,b,c⟩ := decision
  exact ⟨by simpa using lift M a.1 a.2, by simpa using lift (H .fourth) b.1 b.2,
    by simpa using lift R c.1 c.2⟩

end GaussianChains.Bifurcation.Images
