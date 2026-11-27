import BandTaylorFloor
import BandTaylorGain

/-! Soundness of the center/Taylor value comparison over the original full
slack box and the entire floor interval. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Interval

theorem valueTest_sound {q : Oracle} {sample : ℚ → ℚ} {ok : ℚ → Bool}
    {eps : ℚ} {floor : Interval} {B : Box 6} {c : Center} {j : Fin 5} {A : Support}
    {F : ℕ → ℝ → ℝ} {h : ℝ} {u : Fin 6 → ℝ}
    (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x) (hq : FirstOracleSound q F)
    (hsamp : ∀ d : ℚ, d ∈ Set.Icc 0 1 → ok d = true →
      |F 0 (d:ℝ) - (sample d:ℝ)| ≤ (eps:ℝ))
    (hh : floor.Mem h) (hu : B.Mem u) (hs : simplex u)
    (checked : valueTest q sample eps ok floor B c j = true) :
    ¬Stationary A j F h u := by
  simp only [valueTest, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨hf,hc⟩,hok⟩,htok⟩,hlt⟩ := checked
  obtain ⟨hbc,hsc⟩ := validCenter_sound hc
  have hcenter := centerRadius_sound hF hq hsamp hf hbc hsc hok hh
  have hgain := shiftGain_sound hF hq hf hh hu hs hbc hsc
  have hbt : (trialBox j).Mem (liftCenter (trial j)) := fun i => singleton_mem (trial j i)
  have ht := centerRadius_sound hF hq hsamp hf hbt (trial_simplex j) htok hh
  have hcmp : (centerApprox sample floor c : ℝ) + (centerRadius q eps floor B c : ℝ) +
        (shiftGain q floor B c : ℝ) <
      (centerApprox sample floor (trial j) : ℝ) -
        (centerRadius q eps floor (trialBox j) (trial j) : ℝ) := by exact_mod_cast hlt
  intro H
  have hmin : expression .value F h (liftCenter (trial j)) ≤ expression .value F h u := H.1
  linarith only [(abs_le.mp hcenter).2, (abs_le.mp ht).1, hcmp, hgain, hmin]

#print axioms valueTest_sound

end GaussianChains.Band

