import Point22TwoModes
import Point22InteriorTail
import Point22InteriorVariations

/-! Exclude the all-slack contact class by the single-site second variation,
certified second-derivative tail, and quartic root count. -/
noncomputable section
namespace GaussianChains.Point22.Interior
open Real Set

private def V₂ (x : Fin 6 → ℝ) (y : ℝ) := ∑ j, charge j*Curvature.kernel₂ (y-x j)
private def truncated (x : Fin 6 → ℝ) :=
  translatedTwoModes (fun j => 2*π*x j) charge (-factor) (-(factor*(4*q^3)))

private theorem truncated_eval (x : Fin 6 → ℝ) (y : ℝ) :
    truncated x (2*π*y) = ∑ j, charge j*trunc₂ (y-x j) := by
  unfold truncated translatedTwoModes
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub]
  unfold trunc₂
  ring

private theorem approximation (x : Fin 6 → ℝ) (y : ℝ) :
    |truncated x (2*π*y) - V₂ x y| ≤ 75/2 := by
  rw [truncated_eval,V₂,← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin 6, (25/4:ℝ) := by
      apply Finset.sum_le_sum; intro j _
      rw [← mul_sub,abs_mul,show |charge j|=1 by simp [charge,abs_pow]]
      simpa [abs_sub_comm] using (curvature_trunc_error (y-x j)).le
    _ = _ := by norm_num

private def angles (x : Fin 6 → ℝ) (j : Fin 7) := 2*π*liftSite (by decide) x j.val

private theorem truncated_period (x : Fin 6 → ℝ) (θ : ℝ) :
    truncated x (θ+2*π) = truncated x θ := by
  unfold truncated translatedTwoModes
  apply Finset.sum_congr rfl
  intro j _
  rw [show θ+2*π-2*π*x j = (θ-2*π*x j)+2*π by ring,Real.cos_add_two_pi,
    show 2*((θ-2*π*x j)+2*π) = (2*(θ-2*π*x j)+2*π)+2*π by ring,
    Real.cos_add_two_pi,Real.cos_add_two_pi]

/-- At the isolated point the interior of the slack simplex contains no ground state. -/
theorem all_slack_excluded (x : Fin 6 → ℝ)
    (hs : ∀ i, (1/1000:ℝ) < gap (by decide) x i) :
    ¬ IsGroundState (by decide) (1/1000) 22 x := by
  intro hm
  have hd := Curvature.kernel₂_near (x:=0) (by constructor <;> norm_num)
  have hsign (i : Fin 6) : charge i * truncated x (2*π*x i) < 0 := by
    have ha := approximation x (x i)
    have hs' : charge i*V₂ x (x i) ≤ Curvature.kernel₂ 0 := slack_site_necessary hm hs i
    have hb : |charge i * (truncated x (2*π*x i) - V₂ x (x i))| ≤ 75/2 := by
      simpa [abs_mul, charge, abs_pow] using ha
    linarith only [(abs_le.mp hb).2,hs',hd]
  have hzero : angles x 0 = 2*π*x 0 := by simp [angles,liftSite]
  have hlast : angles x (Fin.last 6) = angles x 0+2*π := by
    simp [angles,liftSite]; ring
  have hs_all (j : Fin 7) : (-1:ℝ)^j.val * truncated x (angles x j) < 0 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hlast,truncated_period,hzero]
      norm_num
      simpa [charge] using hsign 0
    · simpa [angles,charge] using hsign i
  have hmono : StrictMono (angles x) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    unfold angles
    apply mul_lt_mul_of_pos_left _ (by positivity)
    have hh := hs i
    change (1/1000:ℝ) < liftSite (by decide) x (i.val+1) - liftSite (by decide) x i.val at hh
    exact sub_pos.mp (lt_trans (by norm_num) hh)
  have hn := no_alternation_translatedTwoModes (fun j => 2*π*x j)
    (charge (N:=6)) (-factor) (-(factor*(4*q^3))) (angles x) hmono (by linarith [hlast])
  apply hn
  intro i
  change truncated x (angles x i.castSucc)*truncated x (angles x i.succ) < 0
  have ht := mul_pos_of_neg_of_neg (hs_all i.castSucc) (hs_all i.succ)
  have hpow : (-1:ℝ)^i.val * (-1:ℝ)^(i.val+1) = -1 := by
    rw [pow_succ,←mul_assoc,←mul_pow]; norm_num
  change 0 < ((-1:ℝ)^i.val * _) * ((-1:ℝ)^(i.val+1) * _) at ht
  rw [mul_mul_mul_comm, hpow,neg_one_mul] at ht
  linarith

theorem groundState_has_contact {x : Fin 6 → ℝ} (hm : IsGroundState (by decide) (1/1000) 22 x) :
    ∃ i, gap (by decide) x i = 1/1000 := by
  by_contra! h
  exact all_slack_excluded x (fun i => lt_of_le_of_ne (hm.1 i) (h i).symm) hm

#print axioms all_slack_excluded
#print axioms groundState_has_contact
end GaussianChains.Point22.Interior
