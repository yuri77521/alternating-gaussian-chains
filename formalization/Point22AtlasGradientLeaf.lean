import Point22AtlasKernel
import CertRoot
import CertRootDerivative
import ChainScore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! A genuine non-degenerate gradient leaf, visit 434 of the published 3111 atlas.
Only three short ranges of table nodes are needed. Re-evaluate those nodes directly
with nine image terms and certified exponential enclosures, so the small test is
independent of the large fixed-point recurrence. -/

namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds GaussianChains.Root22

private def spotNode : Order → ℕ → Interval
  | .first, p => let I := derivativeBox ((p:ℚ)/32000); ⟨I.1,I.2⟩
  | j, p => atlasNode j p

private theorem spotNode_sound (j : Order) (p : ℕ) (hp : p < 32000) :
    (spotNode j p).Mem (mode (orderIndex j) ((p:ℝ)/32000)) := by
  cases j with
  | value => exact atlasNode_sound _ _ hp
  | second => exact atlasNode_sound _ _ hp
  | first =>
    have hr : (p:ℚ) ≤ 32000 := by exact_mod_cast hp.le
    have H := derivativeBox_sound (d := (p:ℚ)/32000)
      ⟨by linarith [Nat.cast_nonneg (α:=ℚ) p], by linarith⟩
    simpa [spotNode, mode, orderIndex, Interval.Mem, Root22.Encloses,
      (hasDerivAt_kernel22 _).deriv] using H

private def grad434 : Interval :=
  let a := atlasBlockRangeFrom spotNode 3 1 .first 16034 16035
  let b := atlasBlockRangeFrom spotNode 1 1 .first 8000 8002
  let c := atlasBlockRangeFrom spotNode 1 1 .first 7996 7999
  (a.add b.neg).add c

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem gradient434_checked : grad434.hi < -1/5000 := by decide +kernel

/-- Throughout the closed 3D box, the derivative in the middle singleton coordinate
is negative. This certificate covers endpoints and all points between the grid nodes. -/
theorem gradient434_negative {u v w : ℝ}
    (hu : u ∈ Set.Icc (8033/32000) (8034/32000))
    (hv : v ∈ Set.Icc (16034/32000) (16035/32000))
    (hw : w ∈ Set.Icc (24031/32000) (24033/32000)) :
    blockValue 3 1 1 v - blockValue 1 1 1 (v-u) + blockValue 1 1 1 (w-v) <
      -1/5000 := by
  have a := atlasBlockRangeFrom_sound spotNode_sound 3 1 .first
    (first:=16034) (last:=16035) (by decide) (by decide) hv
  have b := atlasBlockRangeFrom_sound spotNode_sound 1 1 .first
    (first:=8000) (last:=8002) (by decide) (by decide) (x:=v-u)
    (by constructor <;> norm_num at * <;> linarith [hu.1,hu.2,hv.1,hv.2])
  have c := atlasBlockRangeFrom_sound spotNode_sound 1 1 .first
    (first:=7996) (last:=7999) (by decide) (by decide) (x:=w-v)
    (by constructor <;> norm_num at * <;> linarith [hv.1,hv.2,hw.1,hw.2])
  have H := Interval.add_mem (Interval.add_mem a (Interval.neg_mem b)) c
  have hcast : (grad434.hi:ℝ) < -1/5000 := by exact_mod_cast gradient434_checked
  exact (show _ ≤ (grad434.hi:ℝ) from by simpa [sub_eq_add_neg] using H.2).trans_lt hcast

noncomputable def sampleSites (u v w : ℝ) : Fin 6 → ℝ := ![0,1/1000,2/1000,u,v,w]

set_option maxRecDepth 20000 in
/-- The three variable block interactions contain all dependence on the middle singleton. -/
theorem gradient434_is_score_derivative (u v w : ℝ) :
    HasDerivAt (fun z => pairScore 22 (sampleSites u z w))
      (blockValue 3 1 1 v - blockValue 1 1 1 (v-u) + blockValue 1 1 1 (w-v)) v := by
  let C := pairScore 22 (sampleSites u 0 w) - blockValue 3 1 0 0 +
    blockValue 1 1 0 (0-u) + blockValue 1 1 0 (w-0)
  have hf (z : ℝ) : pairScore 22 (sampleSites u z w) =
      C + blockValue 3 1 0 z - blockValue 1 1 0 (z-u) - blockValue 1 1 0 (w-z) := by
    unfold C blockValue
    norm_num [pairScore,sampleSites,charge,Fin.sum_univ_succ,Finset.sum_range_succ,
      mode,blockSign,shift,sub_eq_add_neg]
    simp (config := { decide := true }) only [ite_true,ite_false]
    ring_nf
  simp_rw [hf]
  have a := (blockValue_hasDerivAt 3 1 0 v).const_add C
  have b := (blockValue_hasDerivAt 1 1 0 (v-u)).comp v ((hasDerivAt_id v).sub_const u)
  have c := (blockValue_hasDerivAt 1 1 0 (w-v)).comp v ((hasDerivAt_id v).const_sub w)
  convert (a.sub b).sub c using 1 <;> simp [Function.comp_def] <;> ring

theorem gradient434_excludes_max {u v w : ℝ}
    (hu : u ∈ Set.Icc (8033/32000) (8034/32000))
    (hv : v ∈ Set.Icc (16034/32000) (16035/32000))
    (hw : w ∈ Set.Icc (24031/32000) (24033/32000)) :
    ¬ IsLocalMax (fun z => pairScore 22 (sampleSites u z w)) v := by
  intro hm
  have hz := (gradient434_is_score_derivative u v w).deriv.symm.trans hm.deriv_eq_zero
  linarith [gradient434_negative hu hv hw]

#print axioms gradient434_excludes_max
end GaussianChains.Point22.Atlas
