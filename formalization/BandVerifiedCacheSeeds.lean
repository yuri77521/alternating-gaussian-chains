import Point22AtlasTablesFixed
import Mathlib.Tactic.FinCases

/-! Integer initial data for the three frozen strip tables. Each literal is
checked against the same rational Taylor seed used in the direct grid model. -/
namespace GaussianChains.Band.Fixed
open GaussianChains.Cert GaussianChains.Cert.Nodes


abbrev Ticks := GaussianChains.Point22.Atlas.Tables.Ticks
abbrev State := GaussianChains.Point22.Atlas.Tables.State

def work : ℕ+ := 10^32
def unit : ℕ+ := 10^9
def grid : ℕ+ := 8192

/-- All three widths have denominator four. -/
def widthCode (anchor : Fin 3) : ℤ := match anchor.val with
  | 0 => 32
  | 1 => 33
  | _ => 35

def s (anchor : Fin 3) : ℚ := (widthCode anchor : ℚ)/4
def param (anchor : Fin 3) : ℚ := s anchor / (grid:ℚ)^2

private def initialRatio (anchor : Fin 3) : Ticks := match anchor.val with
  | 0 => ⟨99999988079071755464582525668610, 99999988079071755464582525669453⟩
  | 1 => ⟨99999987706542770721198764257927, 99999987706542770721198764258879⟩
  | _ => ⟨99999986961484805397767066793014, 99999986961484805397767066794219⟩

def factor (anchor : Fin 3) : Ticks := match anchor.val with
  | 0 => ⟨99999976158144932014467164948142, 99999976158144932014467164961606⟩
  | 1 => ⟨99999975413087052733304009574736, 99999975413087052733304009589964⟩
  | _ => ⟨99999973922971310824318932302211, 99999973922971310824318932321479⟩

def init (anchor : Fin 3) : State :=
  ⟨⟨(work:ℕ), (work:ℕ)⟩, initialRatio anchor⟩

def step (anchor : Fin 3) : State → State := GaussianChains.Point22.Atlas.Tables.State.advance work (factor anchor)

theorem init_eq (anchor : Fin 3) :
    (init anchor).decode work = gaussianEntry work (param anchor) 0 := by
  fin_cases anchor <;> apply congrArg₂ Entry.mk <;> decide +kernel

theorem factor_eq (anchor : Fin 3) :
    (factor anchor).decode work = seed work (2*param anchor) := by
  fin_cases anchor <;> decide +kernel

theorem iterate_eq (anchor : Fin 3) (i : ℕ) :
    ((step anchor)^[i] (init anchor)).decode work = gaussianEntry work (param anchor) i := by
  induction i with
  | zero => exact init_eq anchor
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change (GaussianChains.Point22.Atlas.Tables.State.advance work (factor anchor) ((step anchor)^[i] (init anchor))).decode work = _
    rw [GaussianChains.Point22.Atlas.Tables.State.decode_advance, factor_eq, ih]
    rfl

#print axioms iterate_eq
end GaussianChains.Band.Fixed
