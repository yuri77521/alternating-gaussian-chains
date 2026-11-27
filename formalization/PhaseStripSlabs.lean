import PhaseStripFactor
import PhaseStripRootsSlope

namespace GaussianChains.PhaseStrip

open GaussianChains.Cert GaussianChains.PackedFace Set Real

/-- Each certified threshold uses strict signs at two floor coordinates.
The two x-boxes enclose cos(2πh) at the lower and upper floor, respectively. -/
structure RootWitness where
  floor : Interval
  xl : Interval
  xu : Interval
  deriving Repr

structure Knot where
  s : ℚ
  q : Interval
  center : RootWitness
  outer : RootWitness
  deriving Repr

def Knot.root (r : Knot) (b : Bool) := if b then r.outer else r.center

def RootWitness.ok (r : RootWitness) (b : Bool) (_s : ℚ) (Q : Interval) : Prop :=
  1/8 ≤ r.floor.lo ∧ r.floor.lo ≤ r.floor.hi ∧ r.floor.hi ≤ 1/6 ∧
  encloses r.xl (xInput r.floor.lo) ∧ encloses r.xu (xInput r.floor.hi) ∧
  0 < (slopeBox b Q r.xl).lo ∧ (slopeBox b Q r.xu).hi < 0
instance (r : RootWitness) (b : Bool) (s : ℚ) (Q : Interval) :
    Decidable (r.ok b s Q) := by unfold RootWitness.ok; infer_instance

def Knot.ok (r : Knot) : Prop := 8 ≤ r.s ∧ r.s ≤ 9 ∧ encloses r.q (qInput r.s) ∧
    r.center.ok false r.s r.q ∧ r.outer.ok true r.s r.q
instance (r : Knot) : Decidable r.ok := by unfold Knot.ok; infer_instance

theorem knot_root (r : Knot) (hr : r.ok) (b : Bool) :
    ((r.root b).floor.lo : ℝ) < criticalFloor b (widthNome r.s) ∧
    criticalFloor b (widthNome r.s) < ((r.root b).floor.hi : ℝ) := by
  obtain ⟨h8,h9,hq,hc,hb⟩ := hr
  have hok : (r.root b).ok b r.s r.q := by cases b <;> assumption
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := hok
  exact criticalFloor_in_bracket b h8 h9 h₁ h₂ h₃ hq h₄ h₅ h₆ h₇

private theorem mem_encloses {A B : Interval} {x : ℝ} (h : encloses A B) (hx : B.Mem x) :
    A.Mem x :=
  ⟨(show (A.lo:ℝ) ≤ B.lo by exact_mod_cast h.1).trans hx.1,
    hx.2.trans (by exact_mod_cast h.2)⟩

theorem knot_nome (r : Knot) (hr : r.ok) : r.q.Mem (widthNome r.s) :=
  mem_encloses hr.2.2.1 (qInput_mem hr.1 hr.2.1)

def stripQ (a b : Knot) : Interval := ⟨a.q.lo,b.q.hi⟩
def stripX (a b : Knot) (outer : Bool) : Interval :=
  ⟨(a.root outer).xu.lo,(b.root outer).xl.hi⟩

private theorem nomeGood {t : ℝ} (ht : t ∈ Icc 8 9) :
    t ∈ {u : ℝ | 0 < u ∧ exp (-(π^2)/u) ≤ faceQ} := by
  have hp : 0 < t := by linarith [ht.1]
  exact ⟨hp, by simpa only [faceQ, neg_div] using (nome_lt_seventeen_fiftieths hp ht.2).le⟩

private theorem knot_width (r : Knot) (hr : r.ok) : (r.s : ℝ) ∈ Icc 8 9 := by
  exact ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2.1⟩

theorem stripQ_mem {a b : Knot} (ha : a.ok) (hb : b.ok) {s : ℝ}
    (hs : s ∈ Icc (a.s:ℝ) (b.s:ℝ)) : (stripQ a b).Mem (widthNome s) := by
  have hp := (nomeGood (knot_width a ha)).1
  have hs' := hp.trans_le hs.1
  exact ⟨(knot_nome a ha).1.trans (nome_strictMonoOn.monotoneOn hp hs' hs.1),
    (nome_strictMonoOn.monotoneOn hs' (hs'.trans_le hs.2) hs.2).trans (knot_nome b hb).2⟩

theorem stripX_mem {a b : Knot} (ha : a.ok) (hb : b.ok) (o : Bool) {s : ℝ}
    (hs : s ∈ Icc (a.s:ℝ) (b.s:ℝ)) : (stripX a b o).Mem (thresholdX o (widthNome s)) := by
  have hok (r : Knot) (hr : r.ok) : (r.root o).ok o r.s r.q := by
    cases o <;> first | exact hr.2.2.2.1 | exact hr.2.2.2.2
  have hA := hok a ha
  have hB := hok b hb
  have hW := (criticalFloor_width_strictAntiOn o).antitoneOn
  have haW := nomeGood (knot_width a ha)
  have hbW := nomeGood (knot_width b hb)
  have hsW := nomeGood (show s ∈ Icc 8 9 from
    ⟨(knot_width a ha).1.trans hs.1, hs.2.trans (knot_width b hb).2⟩)
  have hL : ((b.root o).floor.lo:ℝ) ≤ criticalFloor o (widthNome s) :=
    (knot_root b hb o).1.le.trans (hW hsW hbW hs.2)
  have hU : criticalFloor o (widthNome s) ≤ ((a.root o).floor.hi:ℝ) :=
    (hW haW hsW hs.1).trans (knot_root a ha o).2.le
  have hA' := mem_encloses hA.2.2.2.2.1
    (xInput_mem (hA.1.trans hA.2.1) hA.2.2.1)
  have hB' := mem_encloses hB.2.2.2.1
    (xInput_mem hB.1 (hB.2.1.trans hB.2.2.1))
  have hl' : 1/8 ≤ ((b.root o).floor.lo:ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le.mpr hB.1 :
      ((1/8:ℚ):ℝ) ≤ ((b.root o).floor.lo:ℝ))
  have hu' : ((a.root o).floor.hi:ℝ) ≤ 1/6 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le.mpr hA.2.2.1 :
      ((a.root o).floor.hi:ℝ) ≤ ((1/6:ℚ):ℝ))
  have anti {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1/6) (huv : u ≤ v) :
      cos (2*π*v) ≤ cos (2*π*u) := by
    apply cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr hv),pi_pos]
    · exact mul_le_mul_of_nonneg_left huv (by positivity)
  exact ⟨hA'.1.trans (anti (by linarith) hu' hU),
    (anti (by linarith) (hU.trans hu') hL).trans hB'.2⟩

/-- The common physical-width factor is applied only after subtracting the
two separately enclosed root fractions. -/
def pref (a b : Knot) : Interval := ⟨piLo/(2*b.s^2), piHi/(2*a.s^2)⟩
def slopeRange (a b : Knot) (Yc Yb : Interval) : Interval :=
  let Q := stripQ a b
  let Fc := factorBox false Q (stripX a b false) Yc
  let Fb := factorBox true Q (stripX a b true) Yb
  (pref a b).mul (Fb.add Fc.neg)

def factorChecks (b : Bool) (Q X Y : Interval) : Prop :=
  1/2 ≤ X.lo ∧ X.hi ≤ 7/10 ∧ checkSine X Y ∧ 0 < (denomBox b Q X Y).lo
instance (b : Bool) (Q X Y : Interval) : Decidable (factorChecks b Q X Y) := by
  unfold factorChecks; infer_instance

def slabCheck (a b : Knot) (Yc Yb : Interval) : Prop :=
  factorChecks false (stripQ a b) (stripX a b false) Yc ∧
  factorChecks true (stripQ a b) (stripX a b true) Yb ∧
  0.000209555 < (slopeRange a b Yc Yb).lo ∧ (slopeRange a b Yc Yb).hi < 0.000734655
instance (a b : Knot) (Yc Yb : Interval) : Decidable (slabCheck a b Yc Yb) := by
  unfold slabCheck; infer_instance

private theorem pref_mem {a b : Knot} (ha : a.ok) (_hb : b.ok) {s : ℝ}
    (hs : s ∈ Icc (a.s:ℝ) (b.s:ℝ)) : (pref a b).Mem (π/(2*s^2)) := by
  have hapos : (0:ℝ) < a.s := (nomeGood (knot_width a ha)).1
  have hpos := hapos.trans_le hs.1
  have ha₂ := pow_le_pow_left₀ hapos.le hs.1 2
  have hb₂ := pow_le_pow_left₀ hpos.le hs.2 2
  have hl : (piLo:ℝ) ≤ π := Real.pi_gt_d20.le
  have hu : π ≤ (piHi:ℝ) := Real.pi_lt_d20.le
  unfold pref Interval.Mem
  push_cast
  constructor
  · apply div_le_div₀ pi_pos.le hl (by positivity)
    linarith
  · apply div_le_div₀ (pi_pos.le.trans hu) hu (by positivity)
    linarith

theorem slabCheck_sound {a b : Knot} (ha : a.ok) (hb : b.ok) {Yc Yb : Interval}
    (hh : slabCheck a b Yc Yb) {s : ℝ} (hs : s ∈ Icc (a.s:ℝ) (b.s:ℝ)) :
    0.000209555 < deriv phaseWidth s ∧ deriv phaseWidth s < 0.000734655 := by
  have hw : s ∈ Icc 8 9 := ⟨(knot_width a ha).1.trans hs.1, hs.2.trans (knot_width b hb).2⟩
  have hq := stripQ_mem ha hb hs
  have hf (outer : Bool) (Y : Interval)
      (H : factorChecks outer (stripQ a b) (stripX a b outer) Y) :
      (factorBox outer (stripQ a b) (stripX a b outer) Y).Mem
        (phaseFactor outer (widthNome s) (thresholdX outer (widthNome s))) := by
    obtain ⟨h₁,h₂,h₃,h₄⟩ := H
    have hX := stripX_mem ha hb outer hs
    have hL : (1/2:ℝ) ≤ (stripX a b outer).lo := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le.mpr h₁ : ((1/2:ℚ):ℝ) ≤ ((stripX a b outer).lo:ℝ))
    have hU : ((stripX a b outer).hi : ℝ) ≤ 7/10 := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le.mpr h₂ : ((stripX a b outer).hi:ℝ) ≤ ((7/10:ℚ):ℝ))
    have hc : (7/10:ℝ) ≤ sqrt 2/2 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2), sqrt_nonneg (2:ℝ)]
    exact factorBox_mem outer (exp_pos _).le (nomeGood hw).2
      ⟨hL.trans hX.1,hX.2.trans (hU.trans hc)⟩ hq hX h₃ h₄
  have h := Interval.mul_mem (pref_mem ha hb hs) (Interval.add_mem (hf true Yb hh.2.1)
    (Interval.neg_mem (hf false Yc hh.1)))
  rw [(phaseWidth_hasDerivAt hw.1 hw.2).deriv,sub_eq_add_neg]
  have hlo : (0.000209555:ℝ) < (slopeRange a b Yc Yb).lo := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_lt.mpr hh.2.2.1 :
      ((0.000209555:ℚ):ℝ) < ((slopeRange a b Yc Yb).lo:ℝ))
  have hhi : ((slopeRange a b Yc Yb).hi:ℝ) < 0.000734655 := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_lt.mpr hh.2.2.2 :
      ((slopeRange a b Yc Yb).hi:ℝ) < ((0.000734655:ℚ):ℝ))
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

#print axioms slabCheck_sound

end GaussianChains.PhaseStrip

