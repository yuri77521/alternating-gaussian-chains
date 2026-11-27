import StripSurviving
import StripAmplitude
import StripFiveOne
import StripProfile

/-! Reduction of small floors once the first-harmonic peak conditions on
movable blocks have been verified, using the exhaustive physical support chart. -/
noncomputable section
namespace GaussianChains.Strip
open Real PackedFace

def BroadSmall (s h : ℝ) := 8 ≤ s ∧ s ≤ 9 ∧ h ≤ 7/100
def NarrowSmall (s h : ℝ) := 799/100 ≤ s ∧ s ≤ 801/100 ∧ h ≤ 1/10

theorem supports_zero_four_contacts {h : ℝ} {x : Fin 6 → ℝ} (hh : h<1/6)
    (hx : Feasible positiveSix h x) (hl : largestLast x) (hA : labelledSupport h x={0}) :
    FourContacts h x := by
  refine ⟨1,fun j => ?_⟩
  have hc : ∀ j : Fin 4, ¬boundary ({0}:Support) (j.castLE (by decide : 4 ≤ 6)+1) := by decide
  apply le_antisymm _ (hx _)
  apply le_of_not_gt
  intro H
  have H' := (boundary_iff_slack hh x hl _).mpr H
  rw [hA] at H'
  exact hc _ H'

/-- The only canonical support allowing a block of length five is strictly beaten by
the centered packed triples, at every small floor in either width block. -/
theorem canonical_not_zero {s h : ℝ} (hh : 0<h) {x : Fin 6 → ℝ}
    (hband : BroadSmall s h ∨ NarrowSmall s h) (hx : IsGroundState positiveSix h s x)
    (hl : largestLast x) : labelledSupport h x ≠ {0} := by
  have hs : h ≤ 1/10 := hband.elim (fun H => by linarith [H.2.2]) (fun H => H.2.2)
  intro hA
  exact minimizing_cell_has_no_four_contacts hh x hband hx.2
    (supports_zero_four_contacts (by linarith) hx.1 hl hA)

theorem broad_from_peak_arcs {s h : ℝ} (hh : 0<h) (hB : BroadSmall s h)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) (hl : largestLast x)
    (hA : labelledSupport h x ∈ offEdgeReps) (hn : InPeakArcs x h (labelledSupport h x) (46/100)) :
    False := by
  obtain ⟨h8,h9,hr⟩ := hB
  have he := surviving_supports _ hA (canonical_not_zero hh (Or.inl ⟨h8,h9,hr⟩) hx hl)
    (physical_peak_order hh.le hx.1 _ (by linarith [pi_gt_three]) hn)
  obtain ⟨h0,h2,h4⟩ := dimers_contacts (by linarith) hx.1 hl he
  have hu := three_dimers_amplitude hh.le h0 h2 h4
  have ham := broad_minimizer_amplitude h8 h9 hh.le hr hx.1 hx.2
  have hη : 2*π*h ≤ 44/100 := by
    calc _ ≤ 2*(3.1416:ℝ)*(7/100) := by gcongr; exact pi_lt_d4.le
         _ ≤ _ := by norm_num
  linarith

theorem narrow_from_peak_arcs {s h : ℝ} (hh : 0<h) (hB : NarrowSmall s h)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) (hl : largestLast x)
    (hA : labelledSupport h x ∈ offEdgeReps) (hn : InPeakArcs x h (labelledSupport h x) (42/100)) :
    False := by
  obtain ⟨hs,h801,hr⟩ := hB
  have he := surviving_supports _ hA (canonical_not_zero hh (Or.inr ⟨hs,h801,hr⟩) hx hl)
    (physical_peak_order hh.le hx.1 _ (by linarith [pi_gt_three]) hn)
  by_cases hsmall : 2*π*h ≤ 30/100
  · obtain ⟨h0,h2,h4⟩ := dimers_contacts (by linarith) hx.1 hl he
    have hu := three_dimers_amplitude hh.le h0 h2 h4
    have ham := narrow_minimizer_amplitude hs h801 hh.le hr hx.1 hx.2
    linarith
  · exact even_arcs_impossible hh.le hx.1 _ he (by linarith [pi_gt_three]) (by linarith) hn

/-- Pointwise quantitative input at aligned configurations, extracted from the
fixed-potential profile. The geometric conclusion is the actual lifted midpoint's
membership in one of the allowed peak arcs. -/
theorem peak_arcs_from_profiles {s h d : ℝ} (A : Support) (x : Fin 6 → ℝ)
    (hs : 0 < s) (hd : 0 ≤ d) (hdπ : d ≤ π/2) (hM : 0 < ‖structureFactor x 1‖)
    (hbands : let q := exp (-(π^2)/s)
      16*q^3+10*highTail 2 q < ‖structureFactor x 1‖*sin d ∧
      32*q^3+10*highTail 3 q < ‖structureFactor x 1‖*cos d)
    (hprofiles : ∀ j : Fin 6, j.val < blockCount A →
      ∃ B ψ : ℕ → ℝ, IsLocalMax (profile 0 (exp (-(π^2)/s)) B ψ) (blockMid x h A j) ∧
        (∀ t, profileTerm 0 1 (exp (-(π^2)/s)) B ψ t =
          ‖structureFactor x 1‖*cos (t-(peakIndex A j:ℝ)*(π/2))) ∧
        |B 2| ≤ 8 ∧ ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) :
    InPeakArcs x h A d := by
  have hq1 : exp (-(π^2)/s) < 1 := exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos pi_pos)) hs)
  intro k hk
  have h6 := (count_bounds A).2.1
  obtain ⟨B,ψ,hm,hf,h2,hb⟩ := hprofiles ⟨k,by omega⟩ hk
  obtain ⟨j,hj⟩ := profile_peak (exp_pos _).le hq1 B ψ hb h2 hM hf hm hd hdπ hbands.1 hbands.2
  exact ⟨j,hj.le⟩

end GaussianChains.Strip
