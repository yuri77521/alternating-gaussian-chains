import CertRootValueNumbers
import CertRootTail
import ChainEnergy
import ChainGeometry
import Mathlib.Tactic.FinCases

/-! Enclose the actual ordered six-site image energy on the entire published
root interval. All coordinates vary together; independent interval enclosures
are wide enough here because the root interval has width 10⁻³⁰. -/

namespace GaussianChains.Root22
open GaussianChains.Cert GaussianChains.CertExp

private theorem clip_domain (q : ℚ) : 0 ≤ clip q ∧ clip q ≤ 600 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem expRange_sound {b : Interval} {u : ℝ} (hb : b.Mem u)
    (hu : 0 ≤ u ∧ u ≤ 600) : Encloses (expRange b) (Real.exp (-u)) := by
  have hl : ((clip b.lo):ℝ) ≤ u := by
    simp only [clip, Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_ofNat]
    exact max_le hu.1 ((min_le_right _ _).trans hb.1)
  have hh : u ≤ ((clip b.hi):ℝ) := by
    simp only [clip, Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_ofNat]
    exact (le_min hu.2 hb.2).trans (le_max_right _ _)
  exact negExpRange_sound (clip_domain _).1 (clip_domain _).2 hl hh

private theorem singleImage_sound {d : Box} {x : ℝ} (hd : Encloses d x)
    (hx : |x| ≤ 1) {k : ℤ} (hk : k ∈ Finset.Icc (-4:ℤ) 4) :
    Encloses (singleImage d k) (image x k) := by
  have hi := Interval.add_mem (I := (⟨d.1, d.2⟩ : Interval)) hd (Interval.singleton_mem (k:ℚ))
  have hsq := Interval.mul_mem hi hi
  have harg := Interval.mul_mem (Interval.singleton_mem 22) hsq
  push_cast at harg
  have hk' := Finset.mem_Icc.mp hk
  have hl : (-4:ℝ) ≤ k := by exact_mod_cast hk'.1
  have hu : (k:ℝ) ≤ 4 := by exact_mod_cast hk'.2
  have H := expRange_sound harg (show 0 ≤ 22*((x+k)*(x+k)) ∧ 22*((x+k)*(x+k)) ≤ 600 from
    ⟨by nlinarith [sq_nonneg (x+k)], by
      nlinarith [mul_nonneg (show 0 ≤ x+k+5 by linarith [(abs_le.mp hx).1])
        (show 0 ≤ 5-(x+k) by linarith [(abs_le.mp hx).2])]⟩)
  simpa only [singleImage, image, pow_two, neg_mul] using H

theorem kernelBox_sound {d : Box} {x : ℝ} (hd : Encloses d x) (hx : |x| ≤ 1) :
    Encloses (kernelBox d) (GaussianChains.kernel 22 x) := by
  have hm := sumBox_sound (fun k hk => singleImage_sound hd hx (k := k) hk)
  have hr : Encloses (-tailRadius, tailRadius)
      ((∑' k, image x k) - ∑ k ∈ Finset.Icc (-4:ℤ) 4, image x k) := by
    simpa [Encloses, tailRadius] using abs_le.mp (image_tail_bound hx)
  simpa [kernelBox, GaussianChains.kernel, image] using addBox_sound hm hr

theorem energyBox_sound {coords : Fin 6 → Box} {x : Fin 6 → ℝ}
    (hm : ∀ i, Encloses (coords i) (x i)) (hb : ∀ i j, |x j-x i| ≤ 1) :
    Encloses (energyBox coords) (imageEnergy 22 x) := by
  have pair (i j : Fin 6) :=
    scaleBox_sound (kernelBox_sound (subBox_sound (hm j) (hm i)) (hb i j)) (chargeQ i * chargeQ j)
  have s := sumBox_sound (s := (Finset.univ : Finset (Fin 6)))
    (fun i _ => sumBox_sound (s := (Finset.univ : Finset (Fin 6))) (fun j _ => pair i j))
  have H := subBox_sound (show Encloses (1,1) 1 by norm_num [Encloses])
    (scaleBox_sound s (1/6))
  simpa [energyBox, imageEnergy, chargeQ, charge] using H

noncomputable def reflectedSites (r : ℝ) : Fin 6 → ℝ := ![-1/1000,0,1/1000,r,1/2,1-r]

/-- All six gaps of the reflected representative, including the gap across the cut. -/
theorem reflected_gap_word (r : ℝ) :
    gap (by decide) (reflectedSites r) =
      ![1/1000,1/1000,r-1/1000,1/2-r,1/2-r,r-1/1000] := by
  funext i
  fin_cases i <;> norm_num [gap, liftSite, reflectedSites] <;> ring

theorem reflected_feasible {r : ℝ} (hr : (lowerRoot:ℝ) ≤ r ∧ r ≤ (upperRoot:ℝ)) :
    Feasible (by decide) (1/1000) (reflectedSites r) := by
  have hr₁ : 1/5 ≤ r :=
    (by norm_num [lowerRoot] : (1:ℝ)/5 ≤ (lowerRoot:ℝ)).trans hr.1
  have hr₂ : r ≤ 3/10 := hr.2.trans (by norm_num [upperRoot])
  intro i
  rw [reflected_gap_word]
  fin_cases i <;> norm_num <;> linarith

theorem reflection_energy_box {r : ℝ} (h : (lowerRoot:ℝ) ≤ r ∧ r ≤ (upperRoot:ℝ)) :
    Encloses (energyBox coordinateBoxes) (imageEnergy 22 (reflectedSites r)) := by
  have hm (i : Fin 6) : Encloses (coordinateBoxes i) (reflectedSites r i) := by
    fin_cases i <;> norm_num [coordinateBoxes, reflectedSites, Encloses] at * <;>
      first | exact h | exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hb (i : Fin 6) : -1/1000 ≤ reflectedSites r i ∧ reflectedSites r i ≤ 4/5 := by
    have hh : 1/5 ≤ r ∧ r ≤ 3/10 :=
      ⟨(by norm_num [lowerRoot] : (1:ℝ)/5 ≤ (lowerRoot:ℝ)).trans h.1,
       h.2.trans (by norm_num [upperRoot])⟩
    fin_cases i <;> norm_num [reflectedSites] <;> constructor <;> linarith [hh.1,hh.2]
  exact energyBox_sound hm fun i j => abs_le.mpr
    ⟨by linarith [(hb i).2,(hb j).1], by linarith [(hb i).1,(hb j).2]⟩

theorem reflection_energy_enclosed {r : ℝ} (hr : (lowerRoot:ℝ) ≤ r ∧ r ≤ (upperRoot:ℝ)) :
    (energyLower:ℝ) < imageEnergy 22 (reflectedSites r) ∧
      imageEnergy 22 (reflectedSites r) < (energyUpper:ℝ) := by
  have h := reflection_energy_box hr
  exact ⟨(Rat.cast_lt.mpr check_energy.1).trans_le h.1,
    h.2.trans_lt (Rat.cast_lt.mpr check_energy.2)⟩

/-- In physical period-one units this is the original primed, ordered image sum. -/
theorem reflection_physical_energy_enclosed {r : ℝ}
    (hr : (lowerRoot:ℝ) ≤ r ∧ r ≤ (upperRoot:ℝ)) :
    (energyLower:ℝ) < physicalEnergy 22 1 (reflectedSites r) ∧
      physicalEnergy 22 1 (reflectedSites r) < (energyUpper:ℝ) := by
  rw [physicalEnergy_eq_imageEnergy (N := 6) (by decide) 22 1
    (by norm_num) (by norm_num) (reflectedSites r)]
  simpa using reflection_energy_enclosed hr

#print axioms reflection_energy_enclosed
#print axioms reflection_physical_energy_enclosed
end GaussianChains.Root22
