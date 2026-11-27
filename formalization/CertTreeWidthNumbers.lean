import CertTreeWidth
import CertTreeWidthSamples
import Mathlib.Data.Fin.VecNotation

/-! Rational replay of all three width-slabs in Appendix A.  This file checks
the proposed decimal boxes using certified exponential evaluation, then proves
nine bounds on the entire continuous parameter and displacement domains. -/
namespace GaussianChains.WidthBounds
open FourierBounds PackedFace

private def ratioQ (r : Sample) (j : ℕ) : ℚ := (6/5)^j*r.high^11

private def errorQ (l a r : Sample) (j : ℕ) : ℚ :=
  (2*a.factor*a.high*(2*piHi)^j) *
    ((∑ n ∈ Finset.range 4, ((n+1:ℕ):ℚ)^j *
      max (r.high^((n+1)^2-1)-a.low^((n+1)^2-1)) (a.high^((n+1)^2-1)-l.low^((n+1)^2-1))) +
      5^j*r.high^24/(1-ratioQ r j))

private theorem cast_ratio (r : Sample) (j : ℕ) :
    ((ratioQ r j:ℚ):ℝ) = tailRatio r.high j 5 := by
  norm_num [ratioQ, tailRatio]

private theorem cast_error (l a r : Sample) (j : ℕ) :
    ((errorQ l a r j:ℚ):ℝ) = widthError a.factor (2*(piHi:ℝ)) l.low a.low a.high r.high j := by
  simp [errorQ, widthError, discrepancy, cast_ratio]

private def SlabValid (l a r : Sample) (budget : Fin 3 → ℕ) : Prop :=
  l.Valid ∧ a.Valid ∧ r.Valid ∧ a.width ≤ r.width ∧
  ∀ j : Fin 3, ratioQ r j < 1 ∧ errorQ l a r j ≤ (budget j : ℚ)/10^9

private instance (l a r : Sample) (budget : Fin 3 → ℕ) : Decidable (SlabValid l a r budget) := by
  unfold SlabValid
  infer_instance

private theorem slab_sound {l a r : Sample} {budget : Fin 3 → ℕ} (hd : SlabValid l a r budget)
    {s : ℝ} (hs : s ∈ Set.Icc (l.width:ℝ) (r.width:ℝ)) (x : ℝ) (j : Fin 3) :
    |deriv^[j.val] (matched a.width s) x - deriv^[j.val] (kernel a.width) x| ≤
      (budget j:ℝ)/10^9 := by
  rcases hd with ⟨hL,hA,hR,hAR,herr⟩
  obtain ⟨hl,hlq,_,_⟩ := sample_sound _ hL
  obtain ⟨ha,haq,hbq,hc⟩ := sample_sound _ hA
  obtain ⟨_,_,hrq,_⟩ := sample_sound _ hR
  obtain ⟨hr,he⟩ := herr j
  have hratio : tailRatio (r.high:ℝ) j 5 < 1 := by rw [← cast_ratio]; exact_mod_cast hr
  have hbudget : ((errorQ l a r j : ℚ):ℝ) ≤ (budget j:ℝ)/10^9 := by
    calc
      ((errorQ l a r j:ℚ):ℝ) ≤ ((((budget j:ℚ)/10^9):ℚ):ℝ) := Rat.cast_le.mpr he
      _ = _ := by push_cast; rfl
  rw [cast_error] at hbudget
  exact (width_error_sound ha (hl.trans_le hs.1) hc (by linarith only [pi_right])
    (by exact_mod_cast hL.2.1) (by exact_mod_cast hA.2.1)
    (hlq.trans (nome_mono hl hs.1)) ((nome_mono (hl.trans_le hs.1) hs.2).trans hrq)
    haq hbq ((nome_mono ha (by exact_mod_cast hAR)).trans hrq) (by exact_mod_cast hR.2.2.1)
    _ hratio x).trans hbudget

set_option maxRecDepth 20000 in
private theorem narrow_accept : SlabValid w799 w800 w801 ![42761,539098,6806367] := ⟨w799_valid, w800_valid, w801_valid, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 20000 in
private theorem lower_accept : SlabValid w800 w825 w850 ![1156027,14580271,184224460] := ⟨w800_valid, w825_valid, w850_valid, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 20000 in
private theorem upper_accept : SlabValid w850 w875 w900 ![1309984,16545550,209498225] := ⟨w850_valid, w875_valid, w900_valid, by decide +kernel, by decide +kernel⟩

private theorem width799 : w799.width = 799/100 := rfl
private theorem width800 : w800.width = 8 := rfl
private theorem width801 : w801.width = 801/100 := rfl
private theorem width825 : w825.width = 33/4 := rfl
private theorem width850 : w850.width = 17/2 := rfl
private theorem width875 : w875.width = 35/4 := rfl
private theorem width900 : w900.width = 9 := rfl

/-- Appendix A narrow-slab errors in units of 10⁻⁹. -/
theorem width_799_801 {s : ℝ} (hs : s ∈ Set.Icc (799/100:ℝ) (801/100)) (x : ℝ) (j : Fin 3) :
    |deriv^[j.val] (matched 8 s) x - deriv^[j.val] (kernel 8) x| ≤
      ((![42761,539098,6806367] j:ℕ):ℝ)/10^9 := by
  have h := slab_sound narrow_accept (s:=s) (by simpa [width799, width801] using hs) x j
  simpa [width800] using h

/-- Appendix A lower broad-slab errors in units of 10⁻⁹. -/
theorem width_800_850 {s : ℝ} (hs : s ∈ Set.Icc (8:ℝ) (17/2)) (x : ℝ) (j : Fin 3) :
    |deriv^[j.val] (matched (33/4) s) x - deriv^[j.val] (kernel (33/4)) x| ≤
      ((![1156027,14580271,184224460] j:ℕ):ℝ)/10^9 := by
  have h := slab_sound lower_accept (s:=s) (by simpa [width800, width850] using hs) x j
  simpa [width825] using h

/-- Appendix A upper broad-slab errors in units of 10⁻⁹. -/
theorem width_850_900 {s : ℝ} (hs : s ∈ Set.Icc (17/2:ℝ) 9) (x : ℝ) (j : Fin 3) :
    |deriv^[j.val] (matched (35/4) s) x - deriv^[j.val] (kernel (35/4)) x| ≤
      ((![1309984,16545550,209498225] j:ℕ):ℝ)/10^9 := by
  have h := slab_sound upper_accept (s:=s) (by simpa [width850, width900] using hs) x j
  simpa [width875] using h

end GaussianChains.WidthBounds
