import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Rational enclosures and a finite, closed-box exclusion checker. All numeric tests
use exact rational arithmetic. An unresolved or absent child is represented by a hole. -/
namespace GaussianChains.Cert

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace Interval

def Mem (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def singleton (q : ℚ) : Interval := ⟨q,q⟩
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
def meet (I J : Interval) : Interval := ⟨max I.lo J.lo, min I.hi J.hi⟩
def mul (I J : Interval) : Interval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩

/-- Outward rounding on the positive grid of multiples of 1/scale. -/
def roundOut (I : Interval) (scale : ℕ+) : Interval :=
  ⟨(⌊I.lo * (scale : ℚ)⌋ : ℚ) / scale, (⌈I.hi * (scale : ℚ)⌉ : ℚ) / scale⟩

theorem singleton_mem (q : ℚ) : (singleton q).Mem (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_mem {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x+y) := by
  simpa [Mem, add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem neg_mem {I : Interval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by
  simpa [neg, Mem] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem meet_mem {I J : Interval} {x : ℝ} (hx : I.Mem x) (hy : J.Mem x) :
    (I.meet J).Mem x := by
  simpa [meet, Mem] using And.intro (max_le hx.1 hy.1) (le_min hx.2 hy.2)

private theorem between_prod {a x b t L H : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : L ≤ a*t ∧ a*t ≤ H) (hb : L ≤ b*t ∧ b*t ≤ H) : L ≤ x*t ∧ x*t ≤ H := by
  rcases le_total 0 t with ht|ht
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 ht),
           (mul_le_mul_of_nonneg_right hx.2 ht).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 ht),
           (mul_le_mul_of_nonpos_right hx.1 ht).trans ha.2⟩

theorem mul_mem {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x*y) := by
  apply between_prod hx <;> rw [mul_comm]
  · apply between_prod hy <;> simp [mul, mul_comm]
  · apply between_prod hy <;> simp [mul, mul_comm]

theorem roundOut_mem {I : Interval} {x : ℝ} (hx : I.Mem x) (scale : ℕ+) :
    (I.roundOut scale).Mem x := by
  have hs : (0:ℚ) < scale := by exact_mod_cast scale.2
  have hl : (I.roundOut scale).lo ≤ I.lo :=
    (div_le_iff₀ hs).2 (Int.floor_le _)
  have hh : I.hi ≤ (I.roundOut scale).hi :=
    (le_div_iff₀ hs).2 (Int.le_ceil _)
  exact ⟨(show ((I.roundOut scale).lo : ℝ) ≤ I.lo by exact_mod_cast hl).trans hx.1,
    hx.2.trans (by exact_mod_cast hh)⟩

end Interval

abbrev Box (d : ℕ) := Fin d → Interval
namespace Box

def Mem (B : Box d) (x : Fin d → ℝ) := ∀ i, (B i).Mem (x i)
def Left (B : Box d) (i : Fin d) (u : ℚ) : Box d :=
  Function.update B i ⟨(B i).lo, u⟩
def Right (B : Box d) (i : Fin d) (u : ℚ) : Box d :=
  Function.update B i ⟨u, (B i).hi⟩

theorem split_cover {B : Box d} {x : Fin d → ℝ} (hx : B.Mem x) (i : Fin d) (u : ℚ) :
    (B.Left i u).Mem x ∨ (B.Right i u).Mem x := by
  rcases le_total (x i) (u:ℝ) with h|h
  · left
    intro j
    by_cases e : j = i
    · subst j; simpa [Left] using And.intro (hx i).1 h
    · simpa [Left, Function.update_of_ne e] using hx j
  · right
    intro j
    by_cases e : j = i
    · subst j; simpa [Right] using And.intro h (hx i).2
    · simpa [Right, Function.update_of_ne e] using hx j

def subsetB (B C : Box d) : Bool := decide (∀ i, (C i).lo ≤ (B i).lo ∧ (B i).hi ≤ (C i).hi)

theorem mem_of_subsetB {B C : Box d} (hs : subsetB B C = true) {x : Fin d → ℝ}
    (hx : B.Mem x) : C.Mem x := by
  have hc : ∀ i, (C i).lo ≤ (B i).lo ∧ (B i).hi ≤ (C i).hi := of_decide_eq_true hs
  intro i
  exact ⟨(show ((C i).lo : ℝ) ≤ (B i).lo by exact_mod_cast (hc i).1).trans (hx i).1,
    (hx i).2.trans (by exact_mod_cast (hc i).2)⟩

end Box

/-- At a candidate maximum a feasibility margin and a trial score difference are
nonnegative, a free transfer gradient vanishes, and its second derivative is nonpositive. -/
inductive Quantity
  | feasible (index : ℕ)
  | score (trial : ℕ)
  | gradient (transfer : ℕ)
  | curvature (transfer : ℕ)
  deriving Repr, DecidableEq

def Necessary : Quantity → ℝ → Prop
  | .feasible _, z | .score _, z => 0 ≤ z
  | .gradient _, z => z = 0
  | .curvature _, z => z ≤ 0

def violates : Quantity → Interval → Bool
  | .feasible _, I | .score _, I => decide (I.hi < 0)
  | .gradient _, I => decide (I.hi < 0 ∨ 0 < I.lo)
  | .curvature _, I => decide (0 < I.lo)

theorem violates_sound (k : Quantity) {I : Interval} {z : ℝ} (h : violates k I = true)
    (hz : I.Mem z) : ¬Necessary k z := by
  cases k with
  | feasible n | score n =>
    have hu : I.hi < 0 := of_decide_eq_true h
    exact not_le_of_gt (hz.2.trans_lt (by exact_mod_cast hu))
  | gradient n =>
    have hs : I.hi < 0 ∨ 0 < I.lo := of_decide_eq_true h
    rcases hs with hs|hs
    · exact ne_of_lt (hz.2.trans_lt (by exact_mod_cast hs))
    · exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hs) hz.1)
  | curvature n =>
    have hl : 0 < I.lo := of_decide_eq_true h
    exact not_le_of_gt (lt_of_lt_of_le (by exact_mod_cast hl) hz.1)

inductive Tree (d : ℕ)
  | hole
  | leaf (reason : Quantity)
  | localDomain
  | split (coordinate : Fin d) (cut : ℚ) (left right : Tree d)
  deriving Repr

def accept (bounds : Box d → Quantity → Interval) (target : Option (Box d))
    (B : Box d) : Tree d → Bool
  | .hole => false
  | .leaf k => violates k (bounds B k)
  | .localDomain => match target with
    | none => false
    | some C => B.subsetB C
  | .split i u l r =>
    decide ((B i).lo ≤ u ∧ u ≤ (B i).hi) &&
      accept bounds target (B.Left i u) l && accept bounds target (B.Right i u) r

def Reached (target : Option (Box d)) (x : Fin d → ℝ) : Prop :=
  match target with
  | none => False
  | some B => B.Mem x

/-- With no local target this excludes every candidate in the original continuous
box. With a target it confines all such candidates to the closed target box. The
oracle enclosures and extremum conditions are mathematical premises, to be proved
for the application. Neither values nor bounds supplied by a generator are trusted. -/
theorem accept_sound {bounds : Box d → Quantity → Interval} {target : Option (Box d)}
    {value : (Fin d → ℝ) → Quantity → ℝ} {candidate : (Fin d → ℝ) → Prop}
    (hencl : ∀ B x, B.Mem x → candidate x → ∀ k, (bounds B k).Mem (value x k))
    (hnec : ∀ x, candidate x → ∀ k, Necessary k (value x k))
    (t : Tree d) (B : Box d) (h : accept bounds target B t = true)
    {x : Fin d → ℝ} (hx : B.Mem x) (hc : candidate x) : Reached target x := by
  induction t generalizing B with
  | hole => simp [accept] at h
  | leaf k =>
    exact False.elim (violates_sound k h (hencl B x hx hc k) (hnec x hc k))
  | localDomain =>
    cases target with
    | none => simp [accept] at h
    | some C => exact Box.mem_of_subsetB h hx
  | split i u l r il ir =>
    simp only [accept, Bool.and_eq_true] at h
    rcases Box.split_cover hx i u with hl|hr
    · exact il _ h.1.2 hl
    · exact ir _ h.2 hr

/-- A one-sided upper enclosure suffices for a trial-comparison leaf. -/
theorem score_leaf_excludes {bounds : Box d → Quantity → Interval} {B : Box d}
    {trial : ℕ} {score trialScore : ℝ}
    (h : accept bounds none B (.leaf (.score trial)) = true)
    (hupper : score - trialScore ≤ ((bounds B (.score trial)).hi : ℝ)) :
    score < trialScore := by
  have hn : (bounds B (.score trial)).hi < 0 := of_decide_eq_true h
  exact sub_neg.mp (hupper.trans_lt (by exact_mod_cast hn))

def checkBracket (l r : Interval) : Bool :=
  decide (l.hi < 0 ∧ 0 < r.lo ∨ 0 < l.lo ∧ r.hi < 0)

theorem bracket_sound {l r : Interval} {a b : ℝ} (h : checkBracket l r = true)
    (ha : l.Mem a) (hb : r.Mem b) : a < 0 ∧ 0 < b ∨ 0 < a ∧ b < 0 := by
  have hh : l.hi < 0 ∧ 0 < r.lo ∨ 0 < l.lo ∧ r.hi < 0 := of_decide_eq_true h
  rcases hh with ⟨hl,hr⟩|⟨hl,hr⟩
  · exact Or.inl ⟨ha.2.trans_lt (by exact_mod_cast hl), lt_of_lt_of_le (by exact_mod_cast hr) hb.1⟩
  · exact Or.inr ⟨lt_of_lt_of_le (by exact_mod_cast hl) ha.1, hb.2.trans_lt (by exact_mod_cast hr)⟩

end GaussianChains.Cert
