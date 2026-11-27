import CollisionRigidity
import CollisionSixPairs
import CollisionStrict
import ParticleDeficit
import ClustersLocalizationEnergy
import ChainStrictMinimum

/-! Equality on the full collision closure. After coincident positive and
negative labels cancel, a single positive and a single negative mass remain. -/
noncomputable section
namespace GaussianChains
open Real MeasureTheory Set Localization Occupation ClusterSeries Multiset

theorem firstMoment_bound_and_equality {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) :
    ‖structureFactor x 1‖ ≤ 2 ∧ (‖structureFactor x 1‖ = 2 → ∃ u, RepresentsDipole x u) := by
  obtain ⟨a,hy,_,halign,_⟩ := exists_first_mode_aligned hN x 0 1 hx
  let y := fun i => x i-a
  let A := circleSet hN y
  let d := charts hN y
  have hi := chartDiscrepancy_integrable (occupied A)
    (occupied_intervalIntegrable (measurable_circleSet hN y))
  have hd := chartDiscrepancy_range (occupied A) (occupied_mem_Icc A)
  have hb (n : ℕ) (hn : 0 < n) : arcMode n d = Complex.I * structureFactor y n :=
    arcMode_eq_I_structureFactor hy n hn
  refine ⟨structureFactor_one_le_two hx, fun e => ⟨a, representsDipole_of_translate x a ?_⟩⟩
  have h0 : arcCost d = 0 := by
    change arcCost (charts hN (fun i => x i-a)) = 0
    rw [chart_cost_eq hy, halign, Complex.ofReal_re, e, sub_self]
  apply representsDipole_of_zero_cost y d hi (fun i t _ => hd i t) h0
  intro n hn
  rw [hb n hn, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

theorem collision_energy_bound {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) {x : Fin (2*m) → ℝ}
    (hx : Feasible (by omega) 0 x) :
    dipoleEnergy (2*m) s ≤ imageEnergy s x ∧
      (imageEnergy s x = dipoleEnergy (2*m) s → ∃ u, RepresentsDipole x u) := by
  let q := exp (-(π^2)/s)
  let coeff := 2 * sqrt (π/s) * q
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (by positivity)) hs)
  have hC : 0 < coeff := by dsimp [coeff]; positivity
  have hN : 0 < ((2*m : ℕ):ℝ) := by positivity
  have h := physical_semicircle_deficit hx hq.le hq1 hR
  have hId := normalized_energy_deficit m hm hs x
  dsimp only at hId
  rw [← hId] at h
  change (4-‖structureFactor x 1‖^2)/3 ≤
    ((2*m : ℕ):ℝ) * (imageEnergy s x - dipoleEnergy (2*m) s) / coeff at h
  obtain ⟨h2, he⟩ := firstMoment_bound_and_equality hx
  have hnum : 0 ≤ 4-‖structureFactor x 1‖^2 := by nlinarith [norm_nonneg (structureFactor x 1)]
  have hnon := (div_nonneg hnum (by norm_num : (0:ℝ) ≤ 3)).trans h
  rw [le_div_iff₀ hC, zero_mul] at hnon
  have hdiff := nonneg_of_mul_nonneg_right hnon hN
  refine ⟨by linarith, fun hz => he ?_⟩
  rw [hz, sub_self, mul_zero, zero_div] at h
  nlinarith [norm_nonneg (structureFactor x 1)]

theorem groundState_collision_iff {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (x : Fin (2*m) → ℝ) :
    IsGroundState (by omega) 0 s x ↔ Feasible (by omega) 0 x ∧ ∃ u, RepresentsDipole x u := by
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨hl, he⟩ := collision_energy_bound hm hs hR hx
    have hu := hmin _ (dipoleTrial_feasible m (by omega) 0)
    rw [dipoleTrial_energy] at hu
    exact ⟨hx, he (le_antisymm hu hl)⟩
  · rintro ⟨hx, u, hu⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [hu.imageEnergy m (by omega) hs]
    exact (collision_energy_bound hm hs hR hy).1

/-- The collision-closure clause of Theorem 5, with its published interval. -/
theorem six_collision_classification {s : ℝ} (h8 : 8 ≤ s) (h9 : s ≤ 9) (x : Fin 6 → ℝ) :
    IsGroundState (by decide) 0 s x ↔ Feasible (by decide) 0 x ∧ ∃ u, RepresentsDipole x u := by
  have hs : 0 < s := by linarith
  exact groundState_collision_iff (m := 3) (by decide) hs
    (widthR_gaussian_lt_two_thirds hs h9).le x

/-- The two extra opposite-charge pairs are an arbitrary common multiset
of phases compatible with the labelled cyclic order. -/
theorem six_collision_two_pairs {s : ℝ} (h8 : 8 ≤ s) (h9 : s ≤ 9) (x : Fin 6 → ℝ) :
    IsGroundState (by decide) 0 s x ↔ Feasible (by decide) 0 x ∧
      ∃ u : ℝ, ∃ r : Multiset ℂ, r.card = 2 ∧
        positivePhases x = unitPhase u ::ₘ r ∧ negativePhases x = (-(unitPhase u)) ::ₘ r := by
  simp only [six_collision_classification h8 h9, representsDipole_iff_two_neutral_pairs]

theorem open_infimum_dipole {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) :
    sInf (imageEnergy s '' {x | StrictlyOrdered (N := 2*m) (by omega) x}) = dipoleEnergy (2*m) s := by
  let hN : 0 < 2*m := by omega
  let x := dipoleTrial hN 0
  have hx := (groundState_collision_iff hm hs hR x).2
    ⟨dipoleTrial_feasible m hN 0, 0, dipoleTrial_represents m hN 0⟩
  rw [strict_infimum_eq_minimum hN hs, ← groundState_energy_eq_minimum hx]
  exact dipoleTrial_energy m hN 0 s

theorem dipole_lt_strict_energy {m : ℕ} (hN : 2 < 2*m) {s : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) {x : Fin (2*m) → ℝ}
    (hx : StrictlyOrdered (by omega) x) : dipoleEnergy (2*m) s < imageEnergy s x := by
  have ⟨hb, hc⟩ := collision_energy_bound (m := m) (by omega) hs hR (x := x) (fun i => (hx i).le)
  apply lt_of_le_of_ne hb
  intro he
  obtain ⟨u, hu⟩ := hc he.symm
  exact not_representsDipole_of_strict hN hx u hu

#print axioms six_collision_two_pairs
#print axioms open_infimum_dipole
#print axioms dipole_lt_strict_energy

end GaussianChains
