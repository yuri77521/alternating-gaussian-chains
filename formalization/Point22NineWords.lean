import Point22DipoleCells
import Point22Canonical
import CertRootPairGap
import CertRootFaceConstants
import CertRootWitness
import Point22Score
import ChainMinimum

/-! Energy exclusion of the nine classes with disjoint contacting dipoles.
Both possible cyclic orders of the remaining particles are included. -/

namespace GaussianChains.Point22
open Root22 Set

theorem actual_two_contacts {m : Fin 6 → Bool} {w : Word}
    (hm : matchesWord m w = true) (hw : w.twoDisjointContacts = true) :
    ∃ i j : Fin 6, m i = false ∧ m j = false ∧ i ≠ j ∧ i+1 ≠ j ∧ j+1 ≠ i := by
  obtain ⟨k,rev,he⟩ := (matchesWord_iff m w).mp hm
  have hs : ∃ i j : Fin 6, w.cuts (edgeIndex k rev i) = false ∧
      w.cuts (edgeIndex k rev j) = false ∧ i ≠ j ∧ i+1 ≠ j ∧ j+1 ≠ i := by
    exact (by
      intro W; cases W <;> decide : ∀ W : Word, ∀ k : Fin 6, ∀ rev : Bool,
      W.twoDisjointContacts = true → ∃ i j : Fin 6,
        W.cuts (edgeIndex k rev i) = false ∧ W.cuts (edgeIndex k rev j) = false ∧
        i ≠ j ∧ i+1 ≠ j ∧ j+1 ≠ i) w k rev hw
  simpa only [he] using hs

theorem nine_classes_excluded (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x)
    {w : Word} (hm : matchesWord (actualCuts (1/1000) (gap (by decide) x)) w = true)
    (hw : w.twoDisjointContacts = true) : 0.66807 < imageEnergy 22 x := by
  obtain ⟨i,j,hi,hj,hne,h₁,h₂⟩ := actual_two_contacts hm hw
  have contact (k : Fin 6) (hk : actualCuts (1/1000) (gap (by decide) x) k = false) :
      gap (by decide) x k = 1/1000 := le_antisymm (by simpa [actualCuts] using hk) (hx k)
  have H : ArcBounds (kernel 22) derivKernel 44 :=
    ⟨hasDerivAt_kernel22,by norm_num,derivKernel_zero,derivKernel_half,
      fun _ h => derivKernel_nonpos h,derivKernel_lipschitz⟩
  have gain (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      |r-1/2|^2/2 ≤ kernel 22 r-kernel 22 (1/2) := by
    by_cases h : r ≤ 1/2
    · have hq := kernel_quadratic_gap (r:=r) ⟨hr.1,h⟩
      rw [sq_abs]
      linarith
    · have hq := kernel_quadratic_gap (r:=1-r) ⟨by linarith [hr.2],by linarith⟩
      rw [kernel_reflect] at hq
      rw [sq_abs]
      linarith
  have he := nine_words_energy_lower H (by norm_num : (0:ℝ) ≤ 1/1000) gain x hx i j
    (contact _ hi) (contact _ hj) hne h₁ h₂
  linarith [antipodal_auxiliary_lower]

theorem disjoint_word_ne_ground_state (x : Fin 6 → ℝ) {w : Word}
    (hm : matchesWord (actualCuts (1/1000) (gap (by decide) x)) w = true)
    (hw : w.twoDisjointContacts = true) : ¬IsGroundState (by decide) (1/1000) 22 x := by
  intro h
  have he := nine_classes_excluded x h.1 hm hw
  have hm' := h.2 _ witnessX_feasible
  linarith [witnessX_enclosed.2]

end GaussianChains.Point22
