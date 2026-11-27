import ChainCompact
import Mathlib.Analysis.SpecificLimits.Basic

/-! Collision-free configurations approximate every point of the closed
gap simplex. This does not assume that a collision-free minimizer exists. -/

noncomputable section
open Set Filter Topology Finset
namespace GaussianChains

def strictGapSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {g | (∀ i, 0 < g i) ∧ ∑ i, g i = 1}

theorem closure_strictGapSimplex {N : ℕ} (hN : 0 < N) :
    closure (strictGapSimplex N) = gapSimplex N 0 := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_gapSimplex N 0)
    exact fun g hg => ⟨fun i => (hg.1 i).le, hg.2⟩
  · intro g hg
    let t (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    let mix (n : ℕ) (i : Fin N) := (1 - t n) * g i + t n * (1 / (N : ℝ))
    have hlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hmix : Tendsto mix atTop (𝓝 g) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simpa [mix] using (((tendsto_const_nhds (x := (1:ℝ))).sub hlim).mul
        (tendsto_const_nhds (x := g i))).add (hlim.mul (tendsto_const_nhds (x := 1/(N:ℝ))))
    apply mem_closure_of_tendsto hmix
    apply Eventually.of_forall
    intro n
    have htpos : 0 < t n := by dsimp [t]; positivity
    have htone : t n ≤ 1 := by
      apply (div_le_one (by positivity : (0:ℝ) < n+1)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    refine ⟨fun i => add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr htone) (hg.1 i))
        (mul_pos htpos (one_div_pos.mpr (Nat.cast_pos.mpr hN))), ?_⟩
    simp only [mix, sum_add_distrib, ← mul_sum, hg.2, mul_one]
    simp [Nat.ne_of_gt hN, nsmul_eq_mul]

/-- Every continuous lower bound verified on the strictly ordered class
extends to the collision closure, giving the same infimum. -/
theorem lowerBound_strict_iff_closed {N : ℕ} (hN : 0 < N) {F : (Fin N → ℝ) → ℝ}
    (hF : Continuous F) (r : ℝ) :
    (∀ g ∈ strictGapSimplex N, r ≤ F g) ↔ (∀ g ∈ gapSimplex N 0, r ≤ F g) := by
  constructor
  · intro h
    have sub : strictGapSimplex N ⊆ {g | r ≤ F g} := h
    have c := closure_minimal sub (isClosed_le continuous_const hF)
    simpa [closure_strictGapSimplex hN] using c
  · intro h g hg
    exact h g ⟨fun i => (hg.1 i).le, hg.2⟩

end GaussianChains
