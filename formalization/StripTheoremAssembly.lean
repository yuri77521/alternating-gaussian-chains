import BandGlobal
import StripSmallTheorem
import PackedFaceTheorem
import PhaseStripVerified
import CollisionClassification

/-! Real-variable assembly for Theorem 5 and the independent analytic
classification at small floors. -/
noncomputable section
namespace GaussianChains.Strip
open Set PackedFace Band PhaseStrip Multiset

/-- All displacements admitted by Table 1 give full ground states. Every
ground state has a cyclically translated representative in that table.
The last two clauses have the narrower interval [8,9] of the paper. -/
def TheoremFive : Prop :=
  (∀ {s h : ℝ}, s ∈ Set.Icc (799/100) 9 → h ∈ Set.Ioc 0 (1/6) →
    PhaseRows s h ∧ ∀ x : Fin 6 → ℝ, IsGroundState positiveSix h s x ↔
      ∃ k t, minimizesEnergy s h t ∧ RepresentsFace h x k t) ∧
  (∀ {s : ℝ}, s ∈ Set.Icc 8 9 →
    0.000209555 < deriv phaseWidth s ∧ deriv phaseWidth s < 0.000734655) ∧
  (∀ {s : ℝ}, s ∈ Set.Icc 8 9 → ∀ x : Fin 6 → ℝ,
    IsGroundState positiveSix 0 s x ↔ Feasible positiveSix 0 x ∧
      ∃ u : ℝ, ∃ r : Multiset ℂ, r.card = 2 ∧
        positivePhases x = unitPhase u ::ₘ r ∧ negativePhases x = (-(unitPhase u)) ::ₘ r)

private theorem class_from_packed {s h : ℝ} (hs : s ∈ Set.Icc (799/100) 9)
    (hh : h ∈ Set.Ioc 0 (1/6)) (red : ∀ x, IsGroundState positiveSix h s x → OnFace h x) :
    PhaseRows s h ∧ ∀ x : Fin 6 → ℝ, IsGroundState positiveSix h s x ↔
      ∃ k t, minimizesEnergy s h t ∧ RepresentsFace h x k t := by
  have hs0 : 0 < s := by linarith only [hs.1]
  have hq : Real.exp (-(Real.pi^2)/s) ≤ 17/50 := by
    simpa only [neg_div] using (nome_lt_seventeen_fiftieths hs0 hs.2).le
  exact ⟨(theorem_three s hs0 hq).2.2 h hh.1 hh.2,full_classification_of_onFace hs0 hh red⟩

/-- Unconditional full-simplex classification on the two analytically
covered small-floor rectangles, including their positive upper endpoints. -/
theorem small_floor_full_classification {s h : ℝ} (hh : 0 < h)
    (rect : BroadSmall s h ∨ NarrowSmall s h) :
    PhaseRows s h ∧ ∀ x : Fin 6 → ℝ, IsGroundState positiveSix h s x ↔
      ∃ k t, minimizesEnergy s h t ∧ RepresentsFace h x k t := by
  have hstrip : s ∈ Set.Icc (799/100:ℝ) 9 := by
    rcases rect with H | H
    · exact ⟨by linarith [H.1],H.2.1⟩
    · exact ⟨H.1,by linarith [H.2.1]⟩
  have hmax : h ≤ 1/6 := by rcases rect with H | H <;> linarith only [H.2.2]
  exact class_from_packed hstrip ⟨hh,hmax⟩ (small_floor_reduction hh rect)

/-- The eighteen off-edge supports per scheduled floor are the only
computer-assisted premises in this implication. -/
theorem theorem_five_of_excluded_rows (rows : ∀ slab b i, RowExcluded slab b i) : TheoremFive := by
  refine ⟨?_,fun {_} hs => phaseWidth_deriv_bounds hs,fun {_} hs => six_collision_two_pairs hs.1 hs.2⟩
  intro s h hs hh
  exact class_from_packed hs hh (full_strip_from_exclusions_and_small rows hs hh
    (fun rect x hx => small_floor_reduction hh.1 rect x hx))

/-- The reference Boolean checker implies the same continuous theorem. -/
theorem theorem_five_of_checked_rows (rows : ∀ slab, RowsAccepted slab) : TheoremFive :=
  theorem_five_of_excluded_rows
    (fun slab b i => rowExcluded_of_checkRow slab b i (rows slab b i))

#print axioms small_floor_full_classification
#print axioms theorem_five_of_excluded_rows

end GaussianChains.Strip

