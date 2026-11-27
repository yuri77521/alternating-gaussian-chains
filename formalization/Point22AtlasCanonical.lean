import Point22AtlasCells
import Point22AtlasTree
import Point22Canonical

/-! Canonical physical coordinates for the exact 12-word block cover. -/

namespace GaussianChains.Point22.Atlas

private theorem lifted_lower {x : Fin 6 → ℝ} {h : ℝ} (hx : Feasible (by decide) h x)
    (a n : ℕ) : (n:ℝ)*h ≤ liftSite (by decide) x (a+n)-liftSite (by decide) x a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := hx ⟨(a+n)%6,Nat.mod_lt _ (by decide)⟩
    rw [← gap_lift_period] at hg
    change ((n+1:ℕ):ℝ)*h ≤ liftSite (by decide) x (a+n+1)-liftSite (by decide) x a
    rw [Nat.cast_add,Nat.cast_one]
    linarith

private theorem distances {x : Fin 6 → ℝ} (hx : Feasible (by decide) (1/1000) x)
    (a b : Fin 6) (hab : a.val ≤ b.val) :
    ((b.val:ℝ)-a.val)/1000 ≤ x b - x a ∧
    x b-x a ≤ 1 - (6-(b.val:ℝ)+a.val)/1000 := by
  have hab' : a.val+(b.val-a.val)=b.val := by omega
  have hlo := lifted_lower hx a.val (b.val-a.val)
  rw [hab',liftSite_fin,liftSite_fin,Nat.cast_sub hab] at hlo
  have hb' : b.val+(6+a.val-b.val) = a.val+6 := by omega
  have hhi := lifted_lower hx b.val (6+a.val-b.val)
  rw [hb',liftSite_add_period,liftSite_fin,liftSite_fin,
    Nat.cast_sub (by omega : b.val ≤ 6+a.val),Nat.cast_add] at hhi
  constructor <;> linarith

theorem active_base (w : Word) (i : Fin 6) (hi : Active w i) :
    (baseLabel w i).val = base w i ∧ base w i + sizeAt w (lastIndex w) ≤ 6 := by
  cases w <;> revert i <;> decide

private theorem consecutive_base (w : Word) (i : Fin 5) (hi : Active w i.succ) :
    Active w i.castSucc ∧ base w i.succ = base w i.castSucc + sizeAt w i.castSucc := by
  cases w <;> revert i <;> decide

theorem base_mono (w : Word) (i j : Fin 6) (hij : i < j) (hj : Active w j) :
    Active w i ∧ base w i ≤ base w j := by
  cases w <;> revert i j <;> decide

def ticks (y : Fin 6 → ℝ) (i : Fin 6) := 32000*y i

theorem starts_orderedTicks (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x) :
    OrderedTicks w (ticks (starts w x)) := by
  intro i hi
  obtain ⟨hi',he⟩ := consecutive_base w i hi
  have H := (distances hx (baseLabel w i.castSucc) (baseLabel w i.succ) (by
    rw [(active_base _ _ hi').1,(active_base _ _ hi).1,he]; omega)).1
  rw [(active_base _ _ hi').1,(active_base _ _ hi).1,he,Nat.cast_add] at H
  change i.succ.val < w.blocks.length at hi
  change i.castSucc.val < w.blocks.length at hi'
  simp only [ticks,starts,if_pos hi,if_pos hi']
  linarith

theorem starts_pair_distance (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x)
    (i j : Fin 6) (hij : i < j) (hj : Active w j) :
    ((startLabel w j:ℝ)-startLabel w i)/1000 ≤ starts w x j-starts w x i ∧
    starts w x j-starts w x i ≤ 1-(6-(startLabel w j:ℝ)+startLabel w i)/1000 := by
  obtain ⟨hi,hm⟩ := base_mono w i j hij hj
  obtain ⟨h₁,h₂⟩ := distances hx (baseLabel w i) (baseLabel w j)
    (by rw [(active_base _ _ hi).1,(active_base _ _ hj).1]; exact hm)
  rw [(active_base _ _ hi).1,(active_base _ _ hj).1] at h₁ h₂
  change i.val < w.blocks.length at hi
  change j.val < w.blocks.length at hj
  simp only [starts,if_pos hi,if_pos hj,startLabel,base] at *
  constructor <;> linarith

theorem starts_rootBox (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x) :
    Cert.Box.Mem (rootBox w) (ticks (starts w x)) := by
  intro i
  by_cases hi : i.val = 0
  · have hi' : i=0 := Fin.ext hi
    subst i
    simp [rootBox, ticks, starts_zero, Cert.Interval.Mem]
  by_cases ha : Active w i
  · obtain ⟨he,hb⟩ := active_base w i ha
    have H := distances hx 0 (baseLabel w i) (Nat.zero_le _)
    rw [he] at H
    have hs : (base w i : ℝ) + sizeAt w (lastIndex w) ≤ 6 := by exact_mod_cast hb
    have ha' : i.val < w.blocks.length := ha
    simp only [rootBox,hi,ha,ha',not_true_eq_false,or_self,if_false,if_true,ticks,starts,
      Cert.Interval.Mem,Rat.cast_zero,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast]
    norm_num at H
    constructor <;> linarith [H.1,H.2,Nat.cast_nonneg (α:=ℝ) (base w i)]
  · have hi' : w.blocks.length ≤ i.val := Nat.le_of_not_gt ha
    simp [rootBox,hi,ha,ticks,inactive_start w x i hi',Cert.Interval.Mem]

private theorem last_facts (w : Word) :
    Active w (lastIndex w) ∧ blockId w 5 = lastIndex w ∧
      offset w 5 = sizeAt w (lastIndex w)-1 := by cases w <;> decide

private theorem before_facts (w : Word) (i : Fin 6) (hi : sameStart w i = true) :
    PreservesCuts w (baseLabel w i) ∧ Active w i ∧ Active w (prevIndex i) ∧
      5+baseLabel w i ≠ 5 ∧ blockId w (5+baseLabel w i) = prevIndex i ∧
      offset w (5+baseLabel w i) = sizeAt w (prevIndex i)-1 := by
  cases w <;> revert i <;> decide

theorem starts_canonicalTicks (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x)
    (hc : CanonicalBlockCut w (gap (by decide) x)) : CanonicalTicks w (ticks (starts w x)) := by
  intro i hi
  obtain ⟨hs,hi',hp',hne,hidx,hoff⟩ := before_facts w i hi
  have he := hc.2 _ hs
  rw [six_gap_eq,cyclicGap,cyclicGap,if_neg hne,if_pos rfl] at he
  have had : 5+baseLabel w i+1=baseLabel w i :=
    (by decide : ∀ k : Fin 6, 5+k+1 = k) _
  have h5 : (5+1:Fin 6) = 0 := by decide
  rw [had,h5] at he
  have hy := physical_placed_of_cuts w x hx hc.1
  have hl := hy 5
  have hm := hy (5+baseLabel w i)
  rw [placed,(last_facts w).2.1,(last_facts w).2.2] at hl
  rw [placed,hidx,hoff] at hm
  have heq : starts w x i = x (baseLabel w i)-x 0 := if_pos hi'
  unfold ticks
  linarith

end GaussianChains.Point22.Atlas
