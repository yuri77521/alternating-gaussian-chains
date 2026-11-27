import BandVerifiedCacheLookup
import BandVerifiedCacheRows
import BandVerifiedCacheSamples0
import BandVerifiedCacheSamples1
import BandVerifiedCacheSamples2

/-! Soundness of the assertions checked on the packed literals. Each
recurrence page starts at the state certified by the preceding page and
checks both endpoints, including the shared final sample. -/
namespace GaussianChains.Band.Fast
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds

def gauss (a : Fin 3) (p : ℕ) : Fixed.Ticks :=
  let v := match a.val with
    | 0 => (Anchor0.gaussLo p, Anchor0.gaussDelta p)
    | 1 => (Anchor1.gaussLo p, Anchor1.gaussDelta p)
    | _ => (Anchor2.gaussLo p, Anchor2.gaussDelta p)
  ⟨v.1, v.1 + v.2⟩

def stateAt (a : Fin 3) (p : ℕ) : Fixed.State :=
  let v := match a.val with
    | 0 => (Anchor0.ratioLo p, Anchor0.ratioDelta p)
    | 1 => (Anchor1.ratioLo p, Anchor1.ratioDelta p)
    | _ => (Anchor2.ratioLo p, Anchor2.ratioDelta p)
  ⟨gauss a p, ⟨v.1, v.1+v.2⟩⟩

def validateStep (a : Fin 3) (p : ℕ) : Bool :=
  decide (Fixed.step a (stateAt a p) = stateAt a (p+1))

def validatePage (a : Fin 3) (b : ℕ) : Bool :=
  (List.range 32).all (fun j => validateStep a (b*32+j))

theorem gauss_eq {a : Fin 3} (hi : stateAt a 0 = Fixed.init a)
    (hp : ∀ b < 1024, validatePage a b = true) {n : ℕ} (hn : n ≤ 32768) :
    (gauss a n).decode Fixed.work = (Nodes.gaussianEntry Fixed.work (Fixed.param a) n).sample := by
  have hc (p : ℕ) (h : p < 32768) : Fixed.step a (stateAt a p) = stateAt a (p+1) := by
    have hb : p/32 < 1024 := by omega
    have hj : p%32 < 32 := Nat.mod_lt _ (by decide)
    have hv := List.all_eq_true.mp (hp (p/32) hb) (p%32) (List.mem_range.mpr hj)
    rw [show p/32*32+p%32 = p by omega] at hv
    exact of_decide_eq_true hv
  have hs : stateAt a n = (Fixed.step a)^[n] (Fixed.init a) := by
    induction n with
    | zero => exact hi
    | succ n ih => rw [← hc n (by omega), ih (by omega), Function.iterate_succ_apply']
  have h := congrArg (fun st : Fixed.State => st.sample.decode Fixed.work) hs
  exact h.trans (congrArg Nodes.Entry.sample (Fixed.iterate_eq a n))

def expected (a : Fin 3) (j : Order) (p : ℕ) : ℤ × ℤ :=
  let r := Fixed.row a (gauss a) j p
  (r.lo, r.hi)

def ascending (j : Order) : Bool := match j with | .second => true | _ => false

def lastAscending (j : Order) : Bool := match j with | .first => false | _ => !(ascending j)

def checkOrder (a : Fin 3) (j : Order) (p : ℕ) : Bool :=
  let k := turning a j
  let u := ascending j
  let v := lastAscending j
  let edge (f : ℕ → ℤ) := edgeOK f k.1 k.2 u (!u) v p
  decide (rawTicks a j p = expected a j p) &&
    (decide (8192 ≤ p) ||
      (edge (fun i => (rawTicks a j i).1) && edge (fun i => (rawTicks a j i).2)))

def validateNode (a : Fin 3) (p : ℕ) :=
  checkOrder a .value p && checkOrder a .first p && checkOrder a .second p

theorem order_checked {a : Fin 3} {p : ℕ} (h : validateNode a p = true) (j : Order) :
    checkOrder a j p = true := by
  simp only [validateNode, Bool.and_eq_true] at h
  cases j
  · exact h.1.1
  · exact h.1.2
  · exact h.2

/-- Independently checkable, composable finite test. -/
def runChecks (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, p => f p
  | k+1, p => runChecks f k p && runChecks f k (p+2^k)

theorem runChecks_join {f : ℕ → Bool} {k p : ℕ}
    (a : runChecks f k p = true) (b : runChecks f k (p+2^k) = true) :
    runChecks f (k+1) p = true := by simp only [runChecks, a, b, Bool.and_self]

theorem runChecks_sound {f : ℕ → Bool} (k p : ℕ) (h : runChecks f k p = true)
    {n : ℕ} (hlo : p ≤ n) (hhi : n < p + 2^k) : f n = true := by
  induction k generalizing p with
  | zero =>
    rw [pow_zero] at hhi
    have : n = p := by omega
    subst n
    exact h
  | succ k ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hhi
    by_cases H : n < p+2^k
    · exact ih p ha hlo H
    · exact ih (p+2^k) hb (by omega) (by omega)

end GaussianChains.Band.Fast
