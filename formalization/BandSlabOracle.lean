import BandExecutable
import BandTaylorCache
import CertTreeWidthNumbers
import CertTreeWidthOrder

namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds
open GaussianChains.Strip Interval

noncomputable def Slab.field (s : Slab) (width : ℝ) (p : ℕ) : ℝ → ℝ :=
  deriv^[p] (WidthBounds.matched (s.anchor:ℝ) width)

theorem anchor_range (s : Slab) : s.anchor ∈ Set.Icc (8:ℚ) 9 := by cases s <;> decide +kernel

theorem width_perturbation (s : Slab) {width : ℝ} (hw : s.width.Mem width) (j : Fin 3)
    (x : ℝ) : |s.field width j.val x - deriv^[j.val] (kernel (s.anchor:ℝ)) x| ≤ (s.radius j.val : ℝ) := by
  have eq : Fin.ofNat 3 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  cases s with
  | narrow =>
    have hw' : width ∈ Set.Icc (799/100:ℝ) (801/100) := by simpa [Slab.width, Mem] using hw
    simpa [Slab.field, Slab.anchor, Slab.radius, eq] using WidthBounds.width_799_801 hw' x j
  | lower =>
    have hw' : width ∈ Set.Icc (8:ℝ) (17/2) := by simpa [Slab.width, Mem] using hw
    simpa [Slab.field, Slab.anchor, Slab.radius, eq] using WidthBounds.width_800_850 hw' x j
  | upper =>
    have hw' : width ∈ Set.Icc (17/2:ℝ) 9 := by simpa [Slab.width, Mem] using hw
    simpa [Slab.field, Slab.anchor, Slab.radius, eq] using WidthBounds.width_850_900 hw' x j

theorem oracle_mem (s : Slab) {width : ℝ} (hw : s.width.Mem width) (r : Terminal)
    (I : Interval) (x : ℝ) (hx : I.Mem x) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (s.oracle (buildStripCache s.anchor) (order r) I).Mem (s.field width (order r) x) := by
  have ho : orderIndex (imageOrder (order r)) = order r := by cases r <;> rfl
  have hlt : order r < 3 := by cases r <;> norm_num [order]
  apply pad_mem (y := deriv^[order r] (kernel (s.anchor:ℝ)) x)
  · rw [← ho]
    convert cachedStripRange_sound (anchor_range s) (imageOrder (order r))
      (le_max_left 0 I.lo) (min_le_left 1 I.hi)
      (show ((max 0 I.lo:ℚ):ℝ) ≤ x ∧ x ≤ ((min 1 I.hi:ℚ):ℝ) by
        simpa using And.intro (max_le h0 hx.1) (le_min h1 hx.2)) using 1
    rw [ho]
  · exact width_perturbation s hw ⟨_,hlt⟩ x

theorem realTest_sound (s : Slab) {width h : ℝ} (hw : s.width.Mem width)
    (hF : ∀ x, HasDerivAt (s.field width 0) (s.field width 1 x) x)
    {floor : Interval} {B : Box 6} {u : Fin 6 → ℝ} (A : Support) (j : Fin 5)
    (hh : floor.Mem h) (h0 : 0 ≤ h) (h6 : h ≤ 1/6) (hm : B.Mem u) (hs : simplex u)
    (w : Witness) (pass : realTest s (buildStripCache s.anchor) floor A j B w = true) :
    ¬Stationary A j (s.field width) h u := by
  cases w with
  | transfer r => exact testLeaf_sound (oracle_mem s hw) hh h0 h6 hm hs r pass
  | centered c =>
    apply cached_valueTest_sound (anchor_range s) hF _ _ hh hm hs pass
    · exact oracle_mem s hw (.gradient 0)
    · intro x _
      exact width_perturbation s hw (0 : Fin 3) x

end GaussianChains.Band
