import Point22SixScore
import Point22Pairs
import ChainScore
import PackedFaceGeometry
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Fin

/-! Real-space comparison on the *entire* two-triple face. The internal
second differences cost O(h²) uniformly in the distance between the triples. -/

namespace GaussianChains.Point22

noncomputable section

def centeredDifference (G : ℝ → ℝ) (h x : ℝ) := G (x+h)-2*G x+G (x-h)

theorem centeredDifference_bound {G D : ℝ → ℝ} {K h : ℝ}
    (hd : ∀ x, HasDerivAt G (D x) x) (hh : 0 ≤ h)
    (lip : ∀ x y, |D x-D y| ≤ K*|x-y|) (x : ℝ) :
    |centeredDifference G h x| ≤ K*h^2 := by
  have H := dipole_mixed_difference (a := x-h) hd hh lip
  rw [sub_add_cancel] at H
  convert H using 2 <;> unfold centeredDifference <;> ring

set_option maxHeartbeats 2000000 in
/-- Exact decomposition of the directed packed-triple energy into an
opposite-pair energy and three spatial second differences. -/
theorem packed_energy_difference (s h t : ℝ) :
    imageEnergy s (PackedFace.sites h t) =
      1 + (kernel s (1/2+t)-kernel s 0)/3 +
      (centeredDifference (kernel s) h (1/2+t+h) +
       centeredDifference (kernel s) h (1/2+t-h) -
       2*centeredDifference (kernel s) h h)/3 := by
  rw [imageEnergy_eq_pairScore (by decide),six_score_terms]
  generalize kernel s = G
  simp only [show PackedFace.sites h t 0 = 0 from rfl,
    show PackedFace.sites h t 1 = h from rfl, show PackedFace.sites h t 2 = 2*h from rfl,
    show PackedFace.sites h t 3 = 1/2+t from rfl,
    show PackedFace.sites h t 4 = 1/2+t+h from rfl,
    show PackedFace.sites h t 5 = 1/2+t+2*h from rfl,centeredDifference,Nat.cast_ofNat]
  ring_nf

/-- The lower bound uses the nearest image on either side of the wrap. -/
theorem kernel_nearest_image {d : ℝ} (hl : 0 ≤ d) (hu : d ≤ 1) :
    (1:ℝ)/256 < kernel 22 d := by
  have he : Real.exp (11/2) < 256 := by
    have hb : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
    have h₁ : Real.exp (11:ℝ) < 2.72^11 := by
      rw [show Real.exp (11:ℝ) = (Real.exp 1)^11 by rw [← Real.exp_nat_mul]; norm_num]
      exact pow_lt_pow_left₀ hb (Real.exp_pos _).le (by decide)
    have h₂ : Real.exp (11/2)^2 = Real.exp 11 := by rw [sq, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (11/2), h₂]
  have he' : (1:ℝ)/256 < Real.exp (-(11/2)) := by
    rw [Real.exp_neg, one_div, inv_lt_inv₀ (by norm_num) (Real.exp_pos _)]
    exact he
  obtain ⟨k,hk⟩ : ∃ k : ℤ, |d+(k:ℝ)| ≤ 1/2 := by
    by_cases hc : d ≤ 1/2
    · exact ⟨0,by simpa [abs_of_nonneg hl] using hc⟩
    · exact ⟨-1, by rw [abs_le]; push_cast; constructor <;> linarith⟩
  have hs : Real.exp (-(11/2)) ≤ Real.exp (-22*(d+k)^2) := by
    apply Real.exp_le_exp.mpr
    have hh := sq_le_sq' (abs_le.mp hk).1 (abs_le.mp hk).2
    nlinarith
  have hsum := (kernel_summable 22 d (by norm_num)).le_tsum k
    (fun i _ => (Real.exp_pos _).le)
  exact he'.trans_le (hs.trans hsum)

/-- A usable whole-face comparison with the trial X. This proof also works
at either boundary value of the displacement. -/
theorem entire_packed_face_lower {D : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt (kernel 22) (D x) x)
    (lip : ∀ x y, |D x-D y| ≤ 44*|x-y|)
    (h0 : kernel 22 0 ≤ 1.00001)
    (t : ℝ) (ht : PackedFace.feasible (1/1000) t) :
    0.6679 < imageEnergy 22 (PackedFace.sites (1/1000) t) := by
  have hh : 0 ≤ (1/1000:ℝ) := by norm_num
  have hl := centeredDifference_bound hd hh lip (1/2+t+1/1000)
  have hr := centeredDifference_bound hd hh lip (1/2+t-1/1000)
  have hm := centeredDifference_bound hd hh lip (1/1000)
  have hdom := abs_le.mp ht
  unfold PackedFace.bound at hdom
  have hG := kernel_nearest_image (d := 1/2+t) (by linarith [hdom.1]) (by linarith [hdom.2])
  rw [packed_energy_difference]
  linarith [(abs_le.mp hl).1,(abs_le.mp hr).1,(abs_le.mp hm).2]

end
end GaussianChains.Point22
