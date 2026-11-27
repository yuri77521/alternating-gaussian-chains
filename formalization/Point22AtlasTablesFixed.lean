import CertTreeGridCache
import Point22AtlasTablesTypes
import Mathlib.Algebra.Order.Floor.Ring

/-! Integer-tick implementation of the fixed-point Gaussian recurrence. Its decoded
values agree exactly with the rational recurrence used by the kernel estimates. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains.Cert GaussianChains.Cert.Nodes

def Ticks.rawMul (v w : Ticks) : Ticks :=
  ⟨min (min (v.lo*w.lo) (v.lo*w.hi)) (min (v.hi*w.lo) (v.hi*w.hi)),
   max (max (v.lo*w.lo) (v.lo*w.hi)) (max (v.hi*w.lo) (v.hi*w.hi))⟩

def Ticks.reduce (D : ℕ+) (v : Ticks) : Ticks :=
  ⟨v.lo / (D:ℕ), -(-v.hi / (D:ℕ))⟩

def Ticks.multiply (D : ℕ+) (v w : Ticks) : Ticks := (v.rawMul w).reduce D

theorem Ticks.decode_rawMul (v w : Ticks) (D E : ℕ+) :
    (v.rawMul w).decode (D*E) = (v.decode D).mul (w.decode E) := by
  have h : 0 ≤ (D:ℚ)*(E:ℚ) := by positivity
  simp only [decode, rawMul, Interval.mul, PNat.mul_coe, Nat.cast_mul,
    Int.cast_min, Int.cast_max, Int.cast_mul, div_mul_div_comm,
    min_div_div_right h, max_div_div_right h]

private theorem floor_fraction (i : ℤ) (D : ℕ+) :
    ⌊(i:ℚ)/(D:ℚ)⌋ = i/(D:ℕ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast]

private theorem ceil_fraction (i : ℤ) (D : ℕ+) :
    ⌈(i:ℚ)/(D:ℚ)⌉ = -(-i/(D:ℕ)) := by
  rw [← neg_neg ((i:ℚ)/(D:ℚ)), Int.ceil_neg, ← neg_div, ← Int.cast_neg, floor_fraction]

theorem Ticks.decode_reduce (D : ℕ+) (v : Ticks) :
    (v.reduce D).decode D = (v.decode (D*D)).roundOut D := by
  have h : (D:ℚ) ≠ 0 := by positivity
  have hcancel (i : ℤ) : (i:ℚ)/((D:ℚ)*D)*D = i/D := by field_simp
  simp only [decode, reduce, Interval.roundOut, PNat.mul_coe, Nat.cast_mul,
    hcancel, floor_fraction, ceil_fraction]

theorem Ticks.decode_multiply (D : ℕ+) (v w : Ticks) :
    (v.multiply D w).decode D = ((v.decode D).mul (w.decode D)).roundOut D := by
  rw [multiply, decode_reduce, decode_rawMul]

structure State where
  sample : Ticks
  ratio : Ticks
  deriving Repr, DecidableEq

def State.decode (D : ℕ+) (v : State) : Entry := ⟨v.sample.decode D, v.ratio.decode D⟩

def State.advance (D : ℕ+) (step : Ticks) (v : State) : State :=
  ⟨v.sample.multiply D v.ratio, v.ratio.multiply D step⟩

theorem State.decode_advance (D : ℕ+) (step : Ticks) (v : State) :
    (v.advance D step).decode D = Nodes.advance D (step.decode D) (v.decode D) := by
  simp only [advance, decode, Nodes.advance, Ticks.decode_multiply]

def work : ℕ+ := 10^35
def unit : ℕ+ := 10^11
def grid : ℕ+ := 32000
def param : ℚ := 22/(grid:ℚ)^2
def init : State :=
  ⟨⟨(work:ℕ),(work:ℕ)⟩, ⟨99999997851562523078918291752537091,99999997851562523078918291752537980⟩⟩
def factor : Ticks :=
  ⟨99999995703125092315672505895296732,99999995703125092315672505895310937⟩

theorem init_eq : init.decode work = gaussianEntry work param 0 := by
  apply congrArg₂ Entry.mk <;> decide +kernel
theorem factor_eq : factor.decode work = seed work (2*param) := by decide +kernel

/-- The loop contains only big-integer multiplication, min/max and directed division. -/
def step := State.advance work factor

theorem iterate_eq (i : ℕ) : (step^[i] init).decode work = gaussianEntry work param i := by
  induction i with
  | zero => exact init_eq
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change (State.advance work factor (step^[i] init)).decode work = _
    rw [State.decode_advance, factor_eq, ih]
    rfl

end GaussianChains.Point22.Atlas.Tables

