import ChainGeometry
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence

import Mathlib.Tactic.FunProp

noncomputable section
open Finset Set
namespace GaussianChains

/-- Normalized gaps, without quotienting by a choice of first site. -/
def gapSimplex (N : ℕ) (h : ℝ) : Set (Fin N → ℝ) :=
  {g | (∀ i, h ≤ g i) ∧ ∑ i, g i = 1}

private def extendGap {N : ℕ} (g : Fin N → ℝ) (k : ℕ) : ℝ :=
  if hk : k < N then g ⟨k,hk⟩ else 0

private def prefixSum {N : ℕ} (g : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, extendGap g k

/-- Reconstruct the lifted sites by anchoring the first label at zero. -/
def sitesOfGaps {N : ℕ} (g : Fin N → ℝ) (i : Fin N) : ℝ := prefixSum g i.val

private theorem prefix_total {N : ℕ} (g : Fin N → ℝ) :
    prefixSum g N = ∑ i, g i := by
  unfold prefixSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp [extendGap]

theorem gap_sitesOfGaps {N : ℕ} (hN : 0<N) (g : Fin N → ℝ) (hg : ∑ i, g i=1) (i : Fin N) :
    gap hN (sitesOfGaps g) i = g i := by
  have hs : prefixSum g (i.val+1) = prefixSum g i.val + g i := by
    simp [prefixSum, Finset.sum_range_succ, extendGap, i.isLt]
  by_cases hi : i.val+1 < N
  · rw [gap_interior hN _ i hi]
    change prefixSum g (i.val+1) - prefixSum g i.val = _
    linarith
  · have hl : i.val+1 = N := by omega
    rw [gap_wrap hN _ i hl]
    rw [hl, prefix_total, hg] at hs
    change prefixSum g 0 + 1 - prefixSum g i.val = _
    simpa [prefixSum] using (show 1 - prefixSum g i.val = g i by linarith)

theorem sitesOfGaps_gap {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (i : Fin N) :
    sitesOfGaps (gap hN x) i = x i - x ⟨0,hN⟩ := by
  unfold sitesOfGaps prefixSum
  calc
    _ = ∑ k ∈ range i.val, (liftSite hN x (k+1) - liftSite hN x k) := by
      refine sum_congr rfl (fun k hk => ?_)
      have hkN := lt_trans (mem_range.mp hk) i.isLt
      simp [extendGap, hkN, gap]
    _ = _ := by
      rw [sum_range_sub, liftSite_fin, (liftSite_fin hN x ⟨0,hN⟩ : liftSite hN x 0 = _)]

theorem continuous_sitesOfGaps (N : ℕ) :
    Continuous (sitesOfGaps (N := N)) := by
  apply continuous_pi
  intro i
  unfold sitesOfGaps prefixSum
  apply continuous_finset_sum
  intro k _
  unfold extendGap
  split <;> fun_prop

theorem isClosed_gapSimplex (N : ℕ) (h : ℝ) : IsClosed (gapSimplex N h) := by
  change IsClosed ({g : Fin N → ℝ | ∀ i, h ≤ g i} ∩ {g | ∑ i, g i = 1})
  refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
  · rw [show {g : Fin N → ℝ | ∀ i, h ≤ g i} =
        ⋂ i : Fin N, {g : Fin N → ℝ | h ≤ g i} by ext; simp]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  · fun_prop

theorem isCompact_gapSimplex (N : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    IsCompact (gapSimplex N h) := by
  apply (isCompact_Icc (α := Fin N → ℝ) (a := 0) (b := 1)).of_isClosed_subset
    (isClosed_gapSimplex N h)
  intro g hg
  rcases hg with ⟨hl, ht⟩
  have hn (i : Fin N) : 0 ≤ g i := hh.trans (hl i)
  refine ⟨hn, fun i => ?_⟩
  change g i ≤ 1
  rw [← ht]
  exact single_le_sum (f := g) (fun j _ => hn j) (mem_univ i)

theorem gapSimplex_nonempty {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : h ≤ 1/(N:ℝ)) :
    (gapSimplex N h).Nonempty := by
  refine ⟨fun _ => 1/(N:ℝ), fun _ => hh, ?_⟩
  simp [Nat.ne_of_gt hN, nsmul_eq_mul]

theorem feasible_exists_iff {N : ℕ} (hN : 0<N) (h : ℝ) :
    (∃ x, Feasible hN h x) ↔ h ≤ 1/(N:ℝ) := by
  constructor
  · rintro ⟨x,hx⟩
    exact floor_le_mean hx
  · intro hh
    obtain ⟨g,hg⟩ := gapSimplex_nonempty hN hh
    exact ⟨sitesOfGaps g, fun i => (gap_sitesOfGaps hN g hg.2 i).symm ▸ hg.1 i⟩

end GaussianChains
