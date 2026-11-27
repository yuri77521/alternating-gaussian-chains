import CertRootWitness
import CertRootFaceConstants
import CertRootCurvature
import Point22Packed
import Point22Score
import Mathlib.Analysis.Convex.Deriv

/-! Width 22: compare the trial against every point of the closed packed face.
In its middle half all the Gaussian images are convex. This avoids a one-
dimensional numerical search over the packed family. -/

noncomputable section
namespace GaussianChains.Root22
open Set Point22 GaussianChains.CertExp

private theorem atom_second_nonneg {x : ℝ} (hx : x ∈ Icc (1/5:ℝ) (4/5)) (k : ℤ) :
    0 ≤ secondImage (x+k) := by
  have h : 1/5 ≤ |x+k| := by
    by_cases hk : 0 ≤ k
    · have hk' : 0 ≤ (k:ℝ) := by exact_mod_cast hk
      exact (show 1/5 ≤ x+k by linarith [hx.1]).trans (le_abs_self _)
    · have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      exact (show 1/5 ≤ -(x+k) by linarith [hx.2]).trans (neg_le_abs _)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/5) h 2
  rw [sq_abs] at hs
  exact mul_nonneg (by nlinarith : 0 ≤ 1936*(x+k)^2-44) (Real.exp_nonneg _)

theorem middle_convex : ConvexOn ℝ (Icc (1/5:ℝ) (4/5)) (kernel 22) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun x _ => (hasDerivAt_kernel22 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_kernel22 x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_derivKernel x).hasDerivWithinAt)
  exact fun x hx => tsum_nonneg (atom_second_nonneg (interior_subset hx))

private theorem middle_midpoint {a b : ℝ} (ha : a ∈ Icc (1/5:ℝ) (4/5))
    (hb : b ∈ Icc (1/5:ℝ) (4/5)) :
    kernel 22 ((a+b)/2) ≤ (kernel 22 a + kernel 22 b)/2 := by
  have H := middle_convex.2 ha hb (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [show (a+b)/2 = (1/2)*a + (1/2)*b by ring,
    show (kernel 22 a + kernel 22 b)/2 =
      (1/2)*kernel 22 a + (1/2)*kernel 22 b by ring]
  simpa only [smul_eq_mul] using H

private theorem centered_nonneg {x h : ℝ} (hl : x-h ∈ Icc (1/5:ℝ) (4/5))
    (hu : x+h ∈ Icc (1/5:ℝ) (4/5)) : 0 ≤ centeredDifference (kernel 22) h x := by
  have H := middle_midpoint hl hu
  rw [show (x-h+(x+h))/2=x by ring] at H
  unfold centeredDifference
  linarith

private theorem middle_floor {d : ℝ} (hd : d ∈ Icc (1/4:ℝ) (3/4)) :
    kernel 22 (1/2) ≤ kernel 22 d := by
  have H := middle_midpoint (a := d) (b := 1-d)
    (by constructor <;> linarith [hd.1,hd.2]) (by constructor <;> linarith [hd.1,hd.2])
  rw [show (d+(1-d))/2=1/2 by ring, kernel_reflect] at H
  linarith


private theorem near_integer_floor (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1)
    (hc : d < 1/4 ∨ 3/4 < d) : 1/8 < kernel 22 d := by
  obtain ⟨k,hk⟩ : ∃ k : ℤ, |d+k| ≤ 1/4 := by
    rcases hc with hl | hu
    · exact ⟨0, by simpa [abs_of_nonneg hd.1] using hl.le⟩
    · exact ⟨-1, by rw [abs_le]; push_cast; constructor <;> linarith [hd.2]⟩
  have hsum := (kernel_summable 22 d (by norm_num)).le_tsum k (fun i _ => (Real.exp_pos _).le)
  have hcheck : (1/8:ℚ) < (negExpBox (11/8)).1 := by decide +kernel
  have hreal : (1/8:ℝ) < Real.exp (-(11/8:ℝ)) := by
    have h := (negExpBox_sound (x := 11/8) (by norm_num) (by norm_num)).1
    push_cast at h
    exact (show (1/8:ℝ) < ((negExpBox (11/8)).1:ℝ) by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr hcheck).trans_le h
  apply hreal.trans_le (le_trans (Real.exp_le_exp.mpr ?_) hsum)
  have sqb := sq_le_sq' (abs_le.mp hk).1 (abs_le.mp hk).2
  nlinarith

theorem packed_face_energy_floor (t : ℝ) (ht : PackedFace.feasible (1/1000) t) :
    0.669391180769582 < imageEnergy 22 (PackedFace.sites (1/1000) t) := by
  let d : ℝ := 1/2+t
  have hd : 0 ≤ d ∧ d ≤ 1 := by
    have H := abs_le.mp ht
    unfold PackedFace.bound at H
    dsimp [d]
    constructor <;> linarith [H.1,H.2]
  rw [packed_energy_difference]
  change _ < 1 + (kernel 22 d-kernel 22 0)/3 +
    (centeredDifference (kernel 22) (1/1000) (d+1/1000) +
    centeredDifference (kernel 22) (1/1000) (d-1/1000) -
    2*centeredDifference (kernel 22) (1/1000) (1/1000))/3
  rcases packed_numeric_bounds with ⟨hconst,hnum,h0⟩
  have hself : centeredDifference (kernel 22) (1/1000) (1/1000) < 0 := by
    norm_num [centeredDifference] at hnum ⊢
    exact hnum
  by_cases hmid : d ∈ Icc (1/4:ℝ) (3/4)
  · have ha := centered_nonneg (x := d+1/1000) (h := 1/1000)
      (by constructor <;> linarith [hmid.1,hmid.2]) (by constructor <;> linarith [hmid.1,hmid.2])
    have hb := centered_nonneg (x := d-1/1000) (h := 1/1000)
      (by constructor <;> linarith [hmid.1,hmid.2]) (by constructor <;> linarith [hmid.1,hmid.2])
    linarith [middle_floor hmid]
  · have hoff : d < 1/4 ∨ 3/4 < d := by
      by_contra! H
      exact hmid ⟨H.1,H.2⟩
    have hp := near_integer_floor d hd hoff
    have H := centeredDifference_bound hasDerivAt_kernel22 (by norm_num : (0:ℝ) ≤ 1/1000)
      derivKernel_lipschitz
    linarith [(abs_le.mp (H (d+1/1000))).1, (abs_le.mp (H (d-1/1000))).1]

/-- The trial beats the *entire closed face* by the published strict margin. -/
theorem witness_beats_whole_face (t : ℝ) (ht : PackedFace.feasible (1/1000) t) :
    0.002284370362225 <
      imageEnergy 22 (PackedFace.sites (1/1000) t) - imageEnergy 22 (fun i => (witnessX i : ℝ)) := by
  linarith [packed_face_energy_floor t ht,witnessX_enclosed.2]

theorem physical_trial_beats_whole_face :
    ∃ x : Fin 6 → ℝ, Feasible (by decide) (1/1000) x ∧
      ∀ t : ℝ, PackedFace.feasible (1/1000) t →
        0.002284370362225 <
          physicalEnergy 22 1 (PackedFace.sites (1/1000) t) - physicalEnergy 22 1 x := by
  refine ⟨fun i => (witnessX i:ℝ), witnessX_feasible, ?_⟩
  intro t ht
  have hphys (x : Fin 6 → ℝ) : physicalEnergy 22 1 x = imageEnergy 22 x := by
    simpa using physicalEnergy_eq_imageEnergy (N := 6) (by decide) 22 1
      (by norm_num) (by norm_num) x
  simpa only [hphys] using witness_beats_whole_face t ht

theorem whole_face_no_ground_state (t : ℝ) (ht : PackedFace.feasible (1/1000) t) :
    ¬IsGroundState (by decide) (1/1000) 22 (PackedFace.sites (1/1000) t) := by
  intro hg
  have h := hg.2 _ witnessX_feasible
  linarith [witness_beats_whole_face t ht]

#print axioms witness_beats_whole_face
#print axioms physical_trial_beats_whole_face
end GaussianChains.Root22
