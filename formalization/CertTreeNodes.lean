import CertTree
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! An executable recurrence for every spatial Gaussian sample used by the
seven-image tables. If a = s/M² then the n-th node is exp(-a n²), the ratio
to its successor is exp(-a(2n+1)), and the ratio of successive ratios is exp(-2a).
The same fixed rational grid is applied at every multiplication. -/
namespace GaussianChains.Cert.Nodes
open Interval

structure Entry where
  sample : Interval
  ratio : Interval
  deriving Repr

def advance (scale : ℕ+) (step : Interval) (e : Entry) : Entry :=
  ⟨((e.sample.mul e.ratio).roundOut scale), ((e.ratio.mul step).roundOut scale)⟩

def entry (scale : ℕ+) (initialRatio step : Interval) : ℕ → Entry
  | 0 => ⟨singleton 1, initialRatio⟩
  | n+1 => advance scale step (entry scale initialRatio step n)

theorem entry_sound (scale : ℕ+) {a : ℝ} {initialRatio step : Interval}
    (hi : initialRatio.Mem (Real.exp (-a))) (hs : step.Mem (Real.exp (-2*a)))
    (n : ℕ) :
    (entry scale initialRatio step n).sample.Mem (Real.exp (-a * (n:ℝ)^2)) ∧
    (entry scale initialRatio step n).ratio.Mem (Real.exp (-a * (2*(n:ℝ)+1))) := by
  induction n with
  | zero => simpa [entry] using And.intro (singleton_mem 1) hi
  | succ n ih =>
    have h₁ := roundOut_mem (mul_mem ih.1 ih.2) scale
    have h₂ := roundOut_mem (mul_mem ih.2 hs) scale
    rw [← Real.exp_add] at h₁ h₂
    constructor
    · convert h₁ using 2; push_cast; ring
    · convert h₂ using 2; push_cast; ring

/-- Subdivision algorithms can use the previously checked enclosure at each
step and widen it to any supplied rational endpoints; an inward endpoint must
pass the actual enclosure test too. -/
def covers (outer inner : Interval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

theorem covers_sound {outer inner : Interval} (h : covers outer inner = true)
    {x : ℝ} (hx : inner.Mem x) : outer.Mem x := by
  have hh : outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi := of_decide_eq_true h
  exact ⟨(show (outer.lo:ℝ) ≤ inner.lo by exact_mod_cast hh.1).trans hx.1,
    hx.2.trans (by exact_mod_cast hh.2)⟩

/-- Turns the unscaled samples into Gaussian values at the physical grid nodes.
This includes negative image indices by taking their absolute integer index. -/
theorem image_at_node (scale M : ℕ+) {s : ℝ} {initialRatio step : Interval}
    (hi : initialRatio.Mem (Real.exp (-(s/(M:ℝ)^2))))
    (hs : step.Mem (Real.exp (-2*(s/(M:ℝ)^2)))) (k : ℤ) :
    (entry scale initialRatio step k.natAbs).sample.Mem (Real.exp (-s * ((k:ℝ)/M)^2)) := by
  have he := (entry_sound scale hi hs k.natAbs).1
  have hsq : ((k.natAbs:ℝ))^2 = (k:ℝ)^2 := by
    simpa only [Int.cast_natCast, Int.cast_pow, Nat.cast_pow] using congrArg (fun v : ℤ => (v:ℝ)) (Int.natAbs_sq k)
  convert he using 2
  rw [hsq, div_pow]
  ring

end GaussianChains.Cert.Nodes
