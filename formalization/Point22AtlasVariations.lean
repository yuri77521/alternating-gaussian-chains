import Point22AtlasScoreLink
import Point22Physical
import ChainMinimum
import CertTreeVariations

/-! Certification leaves apply to true extrema of the entire feasible set.
A tied canonical cut is only a choice of coordinates; variations can cross it.
Every contacting edge is unchanged along a block translation, while every
slack edge stays feasible for sufficiently small motions of either sign. -/

namespace GaussianChains.Point22.Atlas
open Set Filter Topology

private theorem gap_translate_value (x : Fin 6 → ℝ) (c : ℝ) (i : Fin 6) :
    gap (by decide) (fun p => x p+c) i = gap (by decide) x i := by
  rw [six_gap_eq,six_gap_eq]
  simp [cyclicGap]

theorem block_path_gaps (w : Word) (y v : Fin 6 → ℝ) (t : ℝ) (i : Fin 6) :
    gap (by decide) (placed w (blockTranslation y v t)) i =
      gap (by decide) (placed w y) i +
        (v (blockId w (i+1)) - v (blockId w i))*t := by
  rw [six_gap_eq,six_gap_eq]
  unfold cyclicGap blockTranslation placed
  ring

theorem ground_transformed {h s : ℝ} {x : Fin 6 → ℝ}
    (hx : IsGroundState (by decide) h s x) (k : Fin 6) (rev : Bool) :
    IsGroundState (by decide) h s (transformed x k rev) := by
  have hf := (feasible_shiftLifts_iff (by decide) h x k).2 hx.1
  have he := imageEnergy_shiftLifts (by decide) (by decide) s x k
  cases rev with
  | false =>
    exact ⟨hf, fun y hy => he.trans_le (hx.2 y hy)⟩
  | true =>
    refine ⟨(feasible_reflectLifts_iff (by decide) h _).2 hf,?_⟩
    intro y hy
    exact (imageEnergy_reflectLifts (by decide) (by decide) s _).trans_le (he.trans_le (hx.2 y hy))

theorem feasible_block_translation (w : Word) (x : Fin 6 → ℝ)
    (hx : Feasible (by decide) (1/1000) x)
    (hg : ∀ i, actualCuts (1/1000) (gap (by decide) x) i = w.cuts i)
    (v : Fin 6 → ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), Feasible (by decide) (1/1000)
      (placed w (blockTranslation (starts w x) v t)) := by
  have he : gap (by decide) (placed w (starts w x)) = gap (by decide) x := by
    have hp := funext (physical_placed_of_cuts w x hx hg)
    conv_rhs => rw [hp]
    exact funext (fun i => (gap_translate_value _ _ i).symm)
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : w.cuts i = false
  · apply Filter.Eventually.of_forall
    intro t
    simpa only [block_path_gaps, contact_inside_block w i hi, he, sub_self, zero_mul,
      add_zero] using hx i
  · have htrue : w.cuts i = true := Bool.eq_true_of_not_eq_false hi
    have hs : (1/1000:ℝ) < gap (by decide) x i := by
      simpa [actualCuts,htrue] using hg i
    have hc : ContinuousAt (fun t : ℝ => gap (by decide) x i +
        (v (blockId w (i+1))-v (blockId w i))*t) 0 := by fun_prop
    have hpos := hc.eventually (lt_mem_nhds <| show (1/1000:ℝ) < gap (by decide) x i +
        (v (blockId w (i+1))-v (blockId w i))*0 by simpa only [mul_zero, add_zero] using hs)
    filter_upwards [hpos] with t ht
    simpa only [block_path_gaps,he] using ht.le

theorem ground_atlas_local_max (w : Word) (x : Fin 6 → ℝ)
    (hx : IsGroundState (by decide) (1/1000) 22 x)
    (hg : ∀ i, actualCuts (1/1000) (gap (by decide) x) i = w.cuts i)
    (v : Fin 6 → ℝ) :
    IsLocalMax (fun t => atlasScore w (blockTranslation (starts w x) v t) (internalScore w)) 0 := by
  have he0 : pairScore 22 x = pairScore 22 (placed w (starts w x)) := by
    have hp := funext (physical_placed_of_cuts w x hx.1 hg)
    conv_lhs => rw [hp]
    simp [pairScore]
  filter_upwards [feasible_block_translation w x hx.1 hg v] with t ht
  have h := (imageEnergy_le_iff_pairScore_ge (by decide) 22 x _).mp (hx.2 _ ht)
  rw [he0,atlasScore_placed,atlasScore_placed] at h
  simpa only [show blockTranslation (starts w x) v 0 = starts w x by
    funext i; simp [blockTranslation]] using h

#print axioms ground_atlas_local_max
end GaussianChains.Point22.Atlas
