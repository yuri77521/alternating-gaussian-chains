import ClustersOddSplit
import ClustersArcCharts
import ClustersLocalizationMiddle

noncomputable section
namespace GaussianChains.Occupation

open Real Set Localization MeasureTheory

/-- A true small semicircle discrepancy produces opposite middle cuts in the
actual periodic occupation, with their published angular locations. -/
theorem opposite_middle_cuts {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ)
    (hJ : arcCost (chartDiscrepancy (occupied (circleSet hN x))) < sqrt 2) :
    ∃ y ∈ Icc (π/4) (3*π/4), ∃ z ∈ Icc (5*π/4) (7*π/4),
      y ∈ circleSet hN x ∧ z ∉ circleSet hN x := by
  let A := circleSet hN x
  let d := chartDiscrepancy (occupied A)
  have hi := chartDiscrepancy_integrable (occupied A)
    (occupied_intervalIntegrable (measurable_circleSet hN x))
  have hd (i : Fin 4) (t : ℝ) (_ : t ∈ Icc 0 (π/2)) : 0 ≤ d i t :=
    (chartDiscrepancy_range (occupied A) (occupied_mem_Icc A) i t).1
  obtain ⟨i,hi₁,t,ht,h₁⟩ := exists_central_agreement d hi hd
    (show (0:Fin 4) ≠ 1 by decide) hJ
  obtain ⟨j,hj₁,u,hu,h₂⟩ := exists_central_agreement d hi hd
    (show (2:Fin 4) ≠ 3 by decide) hJ
  refine ⟨quadrantAngle i t,?_,quadrantAngle j u,?_,?_,?_⟩
  · rcases hi₁ with rfl | rfl <;> change _ ≤ _ ∧ _ ≤ _ <;>
      norm_num [quadrantAngle] <;> constructor <;> linarith [ht.1,ht.2,pi_pos]
  · rcases hj₁ with rfl | rfl <;> change _ ≤ _ ∧ _ ≤ _ <;>
      norm_num [quadrantAngle] <;> constructor <;> linarith [hu.1,hu.2,pi_pos]
  · by_contra hn
    change quadrantAngle i t ∉ A at hn
    have hi' : i.val<2 := by rcases hi₁ with rfl | rfl <;> decide
    exact h₁ (by simp [d,chartDiscrepancy,hi',occupied,hn])
  · intro hp
    change quadrantAngle j u ∈ A at hp
    have hj' : ¬j.val<2 := by rcases hj₁ with rfl | rfl <;> decide
    exact h₂ (by simp [d,chartDiscrepancy,hj',occupied,hp])

/-- Both odd clusters are selected from actual particle labels by the
quantitative discrepancy, permitting cuts in different fundamental periods. -/
theorem odd_split_of_discrepancy {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x)
    (hJ : arcCost (chartDiscrepancy (occupied (circleSet hN x))) < sqrt 2) :
    ∃ y ∈ Icc (π/4) (3*π/4), ∃ z ∈ Icc (5*π/4) (7*π/4),
    let a := cutRepresentative hN x y
    let b := cutRepresentative hN x z
    ∃ p q k l : ℕ, p ≤ q ∧ q ≤ 2*m ∧
      q-p = 2*k+1 ∧ 2*m-(q-p)=2*l+1 ∧ k+l+1=m ∧
      ∀ i < 2*m, (min a b ≤ angle hN x i ∧ angle hN x i < max a b) ↔ p ≤ i ∧ i < q := by
  obtain ⟨y,hy,z,hz,hy',hz'⟩ := opposite_middle_cuts hN x hJ
  exact ⟨y,hy,z,hz,odd_blocks_circle_cuts hx hy' hz'⟩

end GaussianChains.Occupation
