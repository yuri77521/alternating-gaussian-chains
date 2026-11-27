import Point22Physical
import Mathlib.Data.Finset.Max

/-! Exact-support normalization for the block atlas. Among repeated copies
of the same cyclic block word choose a maximal preceding slack gap. Equal
maxima remain admissible. -/

namespace GaussianChains.Point22

def PreservesCuts (w : Word) (k : Fin 6) : Prop := ∀ i, w.cuts (i+k) = w.cuts i

instance (w : Word) (k : Fin 6) : Decidable (PreservesCuts w k) := by
  unfold PreservesCuts
  infer_instance

def CanonicalBlockCut (w : Word) (g : Fin 6 → ℝ) : Prop :=
  (∀ i, actualCuts (1/1000) g i = w.cuts i) ∧
    ∀ j : Fin 6, PreservesCuts w j → g (5+j) ≤ g 5

theorem exists_maximal_preceding (w : Word) (g : Fin 6 → ℝ)
    (hm : ∀ i, actualCuts (1/1000) g i = w.cuts i) :
    ∃ k : Fin 6, PreservesCuts w k ∧ CanonicalBlockCut w (rotate g k) := by
  classical
  let I := Finset.univ.filter (PreservesCuts w)
  have hz : (0:Fin 6) ∈ I := by simp [I,PreservesCuts]
  obtain ⟨k,hk,hle⟩ := I.exists_max_image (fun l => g (5+l)) ⟨0,hz⟩
  have hsym := (Finset.mem_filter.mp hk).2
  refine ⟨k,hsym,?_,?_⟩
  · intro i
    exact (hm (i+k)).trans (hsym i)
  · intro j hj
    have hkj : PreservesCuts w (j+k) := by
      intro i
      rw [← add_assoc, hsym, hj]
    simpa [rotate,add_assoc] using hle (j+k) (by simp [I,hkj])

theorem matchesWord_iff (m : Fin 6 → Bool) (w : Word) :
    matchesWord m w = true ↔ ∃ k : Fin 6, ∃ rev : Bool, ∀ i, m i = w.cuts (edgeIndex k rev i) := by
  unfold matchesWord
  simp only [List.any_eq_true,List.all_eq_true, List.mem_finRange, true_implies,
    true_and, beq_iff_eq]
  constructor
  · rintro ⟨k,rev,_,ht⟩
    exact ⟨k,rev,ht⟩
  · rintro ⟨k,rev,ht⟩
    exact ⟨k,rev,by cases rev <;> simp,ht⟩

theorem exact_support_has_cut (g : Fin 6 → ℝ) (hs : ∑ i, g i = 1) :
    ∃ w k rev, CanonicalBlockCut w (fun i => g (edgeIndex k rev i)) := by
  let m := actualCuts (1/1000) g
  have hlen := actual_word_unique g hs
  obtain ⟨w,hw⟩ := (List.length_pos_iff_exists_mem (l:=words.filter (matchesWord m))).mp (by dsimp [m]; omega)
  obtain ⟨k,rev,hm⟩ := (matchesWord_iff m w).mp (List.mem_filter.mp hw).2
  let u := if rev then k else -k
  have hinv : ∀ i, edgeIndex k rev (edgeIndex u rev i) = i := by
    exact (by decide : ∀ k : Fin 6, ∀ rev : Bool, ∀ i : Fin 6,
      edgeIndex k rev (edgeIndex (if rev then k else -k) rev i) = i) k rev
  let g' := fun i => g (edgeIndex u rev i)
  have h' (i : Fin 6) : actualCuts (1/1000) g' i = w.cuts i := by
    exact (hm _).trans (congrArg w.cuts (hinv i))
  obtain ⟨v,_,hv⟩ := exists_maximal_preceding w g' h'
  refine ⟨w,(if rev then u-v else u+v),rev,?_⟩
  have hind (i : Fin 6) : edgeIndex u rev (i+v) = edgeIndex (if rev then u-v else u+v) rev i :=
    (by decide : ∀ u v : Fin 6, ∀ rev : Bool, ∀ i,
      edgeIndex u rev (i+v) = edgeIndex (if rev then u-v else u+v) rev i) u v rev i
  have he : rotate g' v = fun i => g (edgeIndex (if rev then u-v else u+v) rev i) :=
    funext fun i => congrArg g (hind i)
  exact he ▸ hv

theorem physical_canonical_cut (x : Fin 6 → ℝ) :
    ∃ w k rev, CanonicalBlockCut w (gap (by decide) (transformed x k rev)) := by
  obtain ⟨w,k,rev,h⟩ := exact_support_has_cut _ (sum_gap (by decide) x)
  refine ⟨w,k,rev,?_⟩
  simpa only [show gap (by decide) (transformed x k rev) =
    (fun i => gap (by decide) x (edgeIndex k rev i)) from
    funext fun i => transformed_gap x k i rev] using h

end GaussianChains.Point22
