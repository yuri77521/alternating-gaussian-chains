import BandTaylor
import CertTreeStripCache

/-! Accounting for the physical reference-width grid and the perturbation to
the width being tested. Each trial and center contains exactly fifteen pairs. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.Strip

theorem pairs_card : pairs.card = 15 := by decide +kernel

theorem cached_value_sample {s widthErr : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9)
    {F : ℕ → ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc (0:ℝ) 1, |F 0 x - GaussianChains.kernel (s:ℝ) x| ≤ (widthErr:ℝ))
    (d : ℚ) (hd : d ∈ Set.Icc 0 1) (hok : (buildStripCache s).accurate d = true) :
    |F 0 (d:ℝ) - ((buildStripCache s).taylor d : ℝ)| ≤
      ((taylorBudget 8192 1000000000 20 + widthErr : ℚ) : ℝ) := by
  have hd' : (d:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hd.1, by exact_mod_cast hd.2⟩
  have hRef := cachedStripTaylor_sound hs hd hok
  have ht := abs_sub_le (F 0 (d:ℝ)) (GaussianChains.kernel (s:ℝ) (d:ℝ))
    ((buildStripCache s).taylor d : ℝ)
  push_cast
  linarith only [ht, hw _ hd', hRef]

theorem cached_valueTest_sound {s widthErr : ℚ} (hwidth : s ∈ Set.Icc (8:ℚ) 9)
    {q : Oracle} {floor : Interval} {B : Box 6} {c : Center} {j : Fin 5} {A : Support}
    {F : ℕ → ℝ → ℝ} {h : ℝ} {u : Fin 6 → ℝ}
    (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x) (hq : FirstOracleSound q F)
    (hw : ∀ x ∈ Set.Icc (0:ℝ) 1, |F 0 x - GaussianChains.kernel (s:ℝ) x| ≤ (widthErr:ℝ))
    (hh : floor.Mem h) (hu : B.Mem u) (hs : simplex u)
    (checked : valueTest q (buildStripCache s).taylor (taylorBudget 8192 1000000000 20 + widthErr)
      (buildStripCache s).accurate floor B c j = true) : ¬Stationary A j F h u :=
  valueTest_sound hF hq (cached_value_sample hwidth hw) hh hu hs checked

#print axioms cached_valueTest_sound

end GaussianChains.Band

