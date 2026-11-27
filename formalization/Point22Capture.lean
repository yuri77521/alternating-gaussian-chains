import Point22Hessian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Local contraction of the two short gaps in the signed first-moment gauge. -/
namespace GaussianChains.Point22
open Set

/-- Three sites are (-v,u-v,u). External sites have signs (-,+,-).
Terms depending only on the three external sites may be held fixed. -/
def uncontractedField (G : ℝ → ℝ) (y u v : ℝ) : ℝ := G (y+v) - G (y-u+v) + G (y-u)

def shortGapScore (G : ℝ → ℝ) (p : Point) (u v : ℝ) : ℝ :=
  G (u+v) - G u - G v - uncontractedField G p.1 u v +
    uncontractedField G p.2.1 u v - uncontractedField G p.2.2 u v

/-- The ranges reached by the four terms in each finite-difference formula. -/
structure CaptureBounds (G₂ : ℝ → ℝ) (p : Point) (U V : ℝ) : Prop where
  inner : ∀ x ∈ Icc 0 (U+V), G₂ x < -38
  right : ∀ x ∈ Icc (p.1-U) (p.1+V), 14 < G₂ x
  middle : ∀ x ∈ Icc (p.2.1-U) (p.2.1+V), G₂ x < 7
  left : ∀ x ∈ Icc (p.2.2-U) (p.2.2+V), 14 < G₂ x

theorem captureBounds_of_gaps {G₂ : ℝ → ℝ} {p : Point} {U V : ℝ}
    (hU : U ≤ 2/100) (hV : V ≤ 2/100)
    (hr : p.1-U ∈ Icc (21/100:ℝ) (29/100))
    (hz : p.2.1-p.1 ∈ Icc (21/100:ℝ) (29/100))
    (ht : p.2.2-p.2.1 ∈ Icc (21/100:ℝ) (29/100))
    (hw : 1-V-p.2.2 ∈ Icc (21/100:ℝ) (29/100))
    (hnear : ∀ x ∈ Icc (0:ℝ) (4/100), G₂ x < -38)
    (hside : ∀ x ∈ Icc (21/100:ℝ) (33/100), 14 < G₂ x)
    (hdiag : ∀ x ∈ Icc (42/100:ℝ) (58/100), G₂ x < 7)
    (hrefl : ∀ x, G₂ (1-x) = G₂ x) : CaptureBounds G₂ p U V := by
  constructor
  · intro x hx; exact hnear x ⟨hx.1, by linarith [hx.2]⟩
  · intro x hx; exact hside x ⟨by linarith [hx.1,hr.1], by linarith [hx.2,hr.2]⟩
  · intro x hx; exact hdiag x ⟨by linarith [hx.1,hr.1,hz.1], by linarith [hx.2,ht.1,hw.1]⟩
  · intro x hx
    rw [← hrefl x]
    exact hside (1-x) ⟨by linarith [hx.2,hw.1], by linarith [hx.1,hw.2]⟩

private def jump (D : ℝ → ℝ) (x v : ℝ) := D (x+v)-D x

private theorem jump_mvt {D H : ℝ → ℝ} (hd : ∀ x, HasDerivAt D (H x) x)
    (a : ℝ) {w : ℝ} (hw : 0 < w) :
    ∃ x ∈ Icc a (a+w), jump D a w = H x*w := by
  have hf : Continuous D := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope D H (show a<a+w by linarith) hf.continuousOn
    (fun x _ => hd x)
  refine ⟨x, ⟨hx.1.le,hx.2.le⟩, ?_⟩
  simp only [add_sub_cancel_left] at he
  exact ((eq_div_iff hw.ne').mp he).symm

private def signedJump (D : ℝ → ℝ) (p : Point) (a d w : ℝ) :=
  jump D a w - jump D (p.1+d) w + jump D (p.2.1+d) w - jump D (p.2.2+d) w

private theorem signedJump_bound {D H : ℝ → ℝ} (hd : ∀ x, HasDerivAt D (H x) x)
    {p : Point} {U V a d w : ℝ} (hc : CaptureBounds H p U V)
    (hw : 0<w) (ha : 0≤a) (hA : a+w≤U+V) (hlo : -U≤d) (hhi : d+w≤V) :
    signedJump D p a d w < -59*w := by
  obtain ⟨i, hi, ei⟩ := jump_mvt hd a hw
  obtain ⟨r, hr, er⟩ := jump_mvt hd (p.1+d) hw
  obtain ⟨z, hz, ez⟩ := jump_mvt hd (p.2.1+d) hw
  obtain ⟨t, ht, et⟩ := jump_mvt hd (p.2.2+d) hw
  have hi' := hc.inner i ⟨ha.trans hi.1, hi.2.trans hA⟩
  have hr' := hc.right r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hz' := hc.middle z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have ht' := hc.left t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold signedJump
  rw [ei,er,ez,et]
  linarith only [mul_lt_mul_of_pos_right hi' hw, mul_lt_mul_of_pos_right hr' hw,
    mul_lt_mul_of_pos_right hz' hw, mul_lt_mul_of_pos_right ht' hw]

private theorem field_du {G D : ℝ → ℝ} (hd : ∀ x, HasDerivAt G (D x) x) (y u v : ℝ) :
    HasDerivAt (fun a => uncontractedField G y a v) (jump D (y-u) v) u := by
  have h₀ := (hasDerivAt_const u y).sub (hasDerivAt_id u)
  have h₁ := (hd (y-u+v)).comp u (h₀.add_const v)
  have h₂ := (hd (y-u)).comp u h₀
  convert ((hasDerivAt_const u (G (y+v))).sub h₁).add h₂ using 1
  simp [jump]
  ring

private theorem field_dv {G D : ℝ → ℝ} (hd : ∀ x, HasDerivAt G (D x) x) (y u v : ℝ) :
    HasDerivAt (fun b => uncontractedField G y u b) (jump D (y-u+v) u) v := by
  have h₁ := (hd (y+v)).comp v ((hasDerivAt_id v).const_add y)
  have h₂ := (hd (y-u+v)).comp v ((hasDerivAt_id v).const_add (y-u))
  convert ((h₁.sub h₂).add_const (G (y-u))) using 1
  simp [jump]
  ring_nf

private theorem shortGapScore_du {G D : ℝ → ℝ} (hd : ∀ x, HasDerivAt G (D x) x)
    (p : Point) (u v : ℝ) :
    HasDerivAt (fun a => shortGapScore G p a v) (signedJump D p u (-u) v) u := by
  have he := ((hd (u+v)).comp u ((hasDerivAt_id u).add_const v)).sub (hd u)
  have h := ((((he.sub_const (G v)).sub (field_du hd p.1 u v)).add
    (field_du hd p.2.1 u v)).sub (field_du hd p.2.2 u v))
  convert h using 1
  simp [signedJump,jump,sub_eq_add_neg]

private theorem shortGapScore_dv {G D : ℝ → ℝ} (hd : ∀ x, HasDerivAt G (D x) x)
    (p : Point) (u v : ℝ) :
    HasDerivAt (fun b => shortGapScore G p u b) (signedJump D p v (v-u) u) v := by
  have he := (((hd (u+v)).comp v ((hasDerivAt_id v).const_add u)).sub_const (G u)).sub (hd v)
  have h := (((he.sub (field_dv hd p.1 u v)).add (field_dv hd p.2.1 u v)).sub
    (field_dv hd p.2.2 u v))
  convert h using 1
  simp [signedJump,jump]
  ring_nf

theorem opening_score_derivatives {G D H : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, HasDerivAt D (H x) x)
    {p : Point} {U V u v : ℝ} (hc : CaptureBounds H p U V)
    (hu : 0 < u) (hU : u ≤ U) (hv : 0 < v) (hV : v ≤ V) :
    deriv (fun a => shortGapScore G p a v) u < -59*v ∧
      deriv (fun b => shortGapScore G p u b) v < -59*u := by
  rw [(shortGapScore_du hG p u v).deriv,(shortGapScore_dv hG p u v).deriv]
  exact ⟨signedJump_bound hD hc hv hu.le (by linarith) (by linarith) (by linarith),
    signedJump_bound hD hc hu hv.le (by linarith) (by linarith) (by linarith)⟩

/-- Contracting either positive internal gap at fixed signed first moment
strictly increases the score until both attain the floor. -/
theorem shortGapScore_lt_packed {G D H : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, HasDerivAt D (H x) x)
    {p : Point} {U V h u v : ℝ} (hc : CaptureBounds H p U V)
    (hh : 0<h) (hu : h ≤ u) (hU : u ≤ U) (hv : h ≤ v) (hV : v ≤ V)
    (hn : (u,v) ≠ (h,h)) : shortGapScore G p u v < shortGapScore G p h h := by
  have decU : StrictAntiOn (fun a => shortGapScore G p a v) (Icc h U) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun a => (shortGapScore_du hG p a v).continuousAt)).continuousOn
    intro a ha
    have ha' := interior_subset ha
    have e := (opening_score_derivatives hG hD hc (hh.trans_le ha'.1) ha'.2 (hh.trans_le hv) hV).1
    exact e.trans (by nlinarith)
  have decV : StrictAntiOn (fun b => shortGapScore G p h b) (Icc h V) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun b => (shortGapScore_dv hG p h b).continuousAt)).continuousOn
    intro b hb
    have hb' := interior_subset hb
    have e := (opening_score_derivatives hG hD hc hh (hu.trans hU) (hh.trans_le hb'.1) hb'.2).2
    exact e.trans (by nlinarith)
  rcases hu.eq_or_lt with eu|ltu
  · subst u
    have ltv : h < v := lt_of_le_of_ne hv (fun e => hn (by rw [e]))
    exact decV ⟨le_rfl,hv.trans hV⟩ ⟨hv,hV⟩ ltv
  · exact (decU ⟨le_rfl,hu.trans hU⟩ ⟨hu,hU⟩ ltu).trans_le
      (decV.antitoneOn ⟨le_rfl,hv.trans hV⟩ ⟨hv,hV⟩ hv)

end GaussianChains.Point22
