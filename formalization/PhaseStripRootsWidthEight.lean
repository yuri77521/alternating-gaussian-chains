import PhaseStripRoots
import PhaseStripFactor

/-! The three tighter derivative intervals at s=8 following Table 2. All
input intervals are taken from the row whose 17-place root bracket is used. -/
namespace GaussianChains.PhaseStrip

open GaussianChains.Cert GaussianChains.PackedFace Real Set

theorem table2_phase_width_ends :
    phaseWidth 8 ∈ Ioo (213227981950811/10^17) (213227981950813/10^17) ∧
    phaseWidth 9 ∈ Ioo (258415600646431/10^17) (258415600646433/10^17) := by
  have h1 := table2_critical_floors (r:=row8Center) (by simp [rootRows])
  have h2 := table2_critical_floors (r:=row8Contact) (by simp [rootRows])
  have h3 := table2_critical_floors (r:=row9Center) (by simp [rootRows])
  have h4 := table2_critical_floors (r:=row9Contact) (by simp [rootRows])
  have hA := And.intro h1.1 h1.2.1
  have hB := And.intro h2.1 h2.2.1
  have hC := And.intro h3.1 h3.2.1
  have hD := And.intro h4.1 h4.2.1
  norm_num [row8Center,row8Contact,row9Center,row9Contact,RootRow.lower,RootRow.upper] at hA hB hC hD
  unfold phaseWidth widthNome
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow] at *
  constructor <;> constructor <;> linarith [hA.1,hA.2,hB.1,hB.2,hC.1,hC.2,hD.1,hD.2]

def RootRow.xBox (r : RootRow) : Interval := ⟨r.xRight.lo,r.xLeft.hi⟩

theorem row_x_mem {r : RootRow} (hr : r ∈ rootRows) :
    r.xBox.Mem (thresholdX r.outer (widthNome r.width)) := by
  obtain ⟨_,_,hl,hlu,hu,_,hXl,hXu,_,_⟩ := table_checks_spec hr
  have h₁ := encloses_mem hXl (xInput_mem hl (hlu.le.trans hu))
  have h₂ := encloses_mem hXu (xInput_mem (hl.trans hlu.le) hu)
  have hc := table2_critical_floors hr
  have hu' : (r.upper:ℝ) ≤ 1/6 := by
    simpa using (Rat.cast_le.mpr hu : (r.upper:ℝ) ≤ ((1/6:ℚ):ℝ))
  have hl' : (0:ℝ) ≤ r.lower := by exact_mod_cast (by linarith : (0:ℚ) ≤ r.lower)
  have anti {u v : ℝ} (h₀ : 0 ≤ u) (hπ : v ≤ 1/6) (huv : u ≤ v) :
      cos (2*π*v) ≤ cos (2*π*u) := by
    apply cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hπ pi_pos.le,pi_pos]
    · exact mul_le_mul_of_nonneg_left huv (by positivity)
  exact ⟨h₂.1.trans (anti (hl'.trans hc.1.le) hu' hc.2.1.le),
    (anti hl' (hc.2.1.le.trans hu') hc.1.le).trans h₁.2⟩

private def row8 (outer : Bool) := if outer then row8Contact else row8Center

private def sine8 (outer : Bool) : Interval :=
  if outer then ⟨74291670661926360823/10^20,74291670661926365030/10^20⟩
  else ⟨73388222503592035249/10^20,73388222503592039518/10^20⟩

private def scale8 : Interval := ⟨piLo/128,piHi/128⟩
private def factor8 (o : Bool) := factorBox o (row8 o).qBox (row8 o).xBox (sine8 o)
private def rate8 (o : Bool) := scale8.mul (factor8 o)
private def difference8 := scale8.mul ((factor8 true).add (factor8 false).neg)

private def Interior (a b : ℚ) (I : Interval) : Prop := a < I.lo ∧ I.hi < b
private instance (a b : ℚ) (I : Interval) : Decidable (Interior a b I) := by
  unfold Interior; infer_instance

private theorem interior_sound {a b : ℚ} {I : Interval} {y : ℝ}
    (h : Interior a b I) (hy : I.Mem y) : y ∈ Ioo (a:ℝ) (b:ℝ) :=
  ⟨(Rat.cast_lt.mpr h.1).trans_le hy.1,hy.2.trans_lt (Rat.cast_lt.mpr h.2)⟩

private theorem scale8_mem : scale8.Mem (π/(2*8^2)) := by
  unfold scale8 Interval.Mem
  push_cast
  constructor <;> nlinarith [Real.pi_gt_d20,Real.pi_lt_d20,
    show (piLo:ℝ) = 3.14159265358979323846 by rfl,
    show (piHi:ℝ) = 3.14159265358979323847 by rfl]

section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem sine8_ok (o : Bool) : checkSine (row8 o).xBox (sine8 o) := by
  cases o <;> decide +kernel
private theorem denom8_ok (o : Bool) : 0 < (denomBox o (row8 o).qBox (row8 o).xBox (sine8 o)).lo := by
  cases o <;> decide +kernel
private theorem rates8_ok : Interior (-0.004653798) (-0.004653797) (rate8 false) ∧
    Interior (-0.004095783) (-0.004095782) (rate8 true) ∧
    Interior 0.0005580150 0.0005580151 difference8 := by decide +kernel
end

private theorem factor8_mem (o : Bool) :
    (factor8 o).Mem (phaseFactor o (widthNome 8) (thresholdX o (widthNome 8))) := by
  have hm : row8 o ∈ rootRows := by cases o <;> simp [row8,rootRows]
  have hs : (row8 o).width = 8 := by cases o <;> rfl
  have ho : (row8 o).outer = o := by cases o <;> rfl
  have hQ := (table_checks_spec hm).2.2.2.2.2.1
  have hq : (row8 o).qBox.Mem (widthNome 8) := by
    rw [hs] at hQ
    simpa [widthNome] using encloses_mem hQ (qInput_mem (by norm_num) (by norm_num))
  have hX := row_x_mem hm
  rw [ho, hs] at hX
  have hmax : widthNome 8 ≤ faceQ := strip_nome_le_faceQ (by norm_num) (by norm_num)
  have hc := criticalFloor_spec o (show 0 < widthNome 8 from exp_pos _) hmax
  apply factorBox_mem o (exp_pos _).le hmax (cos_floor_large hc.1.1.le hc.1.2.le)
    hq _ (sine8_ok o) (denom8_ok o)
  simpa using hX

/-- Width-eight derivatives of both implicit critical floors and their difference. -/
theorem phase_derivatives_at_eight :
    deriv (fun s => criticalFloor false (widthNome s)) 8 ∈ Ioo (-0.004653798) (-0.004653797) ∧
    deriv (fun s => criticalFloor true (widthNome s)) 8 ∈ Ioo (-0.004095783) (-0.004095782) ∧
    deriv phaseWidth 8 ∈ Ioo 0.0005580150 0.0005580151 := by
  have hmax : widthNome 8 < faceQ := by
    simpa only [widthNome,faceQ,neg_div] using
      nome_lt_seventeen_fiftieths (s:=8) (by norm_num) (by norm_num)
  rw [(criticalFloor_s_hasDerivAt false (by norm_num) hmax).deriv,
    (criticalFloor_s_hasDerivAt true (by norm_num) hmax).deriv,
    (phaseWidth_hasDerivAt (s:=8) le_rfl (by norm_num)).deriv]
  have h₁ := interior_sound rates8_ok.1 (Interval.mul_mem scale8_mem (factor8_mem false))
  have h₂ := interior_sound rates8_ok.2.1 (Interval.mul_mem scale8_mem (factor8_mem true))
  have h₃ := interior_sound rates8_ok.2.2 (Interval.mul_mem scale8_mem
    (Interval.add_mem (factor8_mem true) (Interval.neg_mem (factor8_mem false))))
  norm_num only [Rat.cast_ofScientific,Rat.cast_neg,sub_eq_add_neg] at *
  exact ⟨h₁,h₂,h₃⟩

#print axioms phase_derivatives_at_eight
#print axioms table2_phase_width_ends

end GaussianChains.PhaseStrip
