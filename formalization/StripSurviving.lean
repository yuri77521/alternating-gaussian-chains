import StripMidpoints
import StripWitness

/-! Remaining canonical supports after circle order. For all-even supports
the same three contacts form actual short dipoles in the labelled energy. -/
noncomputable section
namespace GaussianChains.Strip
open Real PackedFace

/-- The sole canonical support allowing five (or more) sites in one block is {0}. -/
theorem off_edge_lengths : ∀ A : Support, A ∈ offEdgeReps → A ≠ {0} →
    ∀ k : Fin 6, k.val < blockCount A → blockLength A k ≤ 4 := by decide

theorem surviving_supports : ∀ A : Support, A ∈ offEdgeReps → A ≠ {0} →
    descents (peakIndex A) (peakList A).length ≤ 1 → A={1} ∨ A={1,3} := by decide

theorem peak_index_formula : ∀ A : Support, ∀ k : Fin 6, k.val < blockCount A →
    peakIndex A k = 2*(blockStart A k % 2) + (if blockLength A k % 2=0 then 1 else 0) := by decide

theorem dimers_contacts {h : ℝ} (hh : h < 1/6) {x : Fin 6 → ℝ}
    (hx : Feasible positiveSix h x) (hl : largestLast x)
    (he : labelledSupport h x={1} ∨ labelledSupport h x={1,3}) :
    gap positiveSix x 0=h ∧ gap positiveSix x 2=h ∧ gap positiveSix x 4=h := by
  have hb : ∀ A : Support, A={1} ∨ A={1,3} → ∀ i : Fin 6,
      i=0 ∨ i=2 ∨ i=4 → ¬ boundary A i := by decide
  have fixed (i : Fin 6) (hi : i=0 ∨ i=2 ∨ i=4) : gap positiveSix x i=h :=
    le_antisymm (le_of_not_gt (fun ht => hb _ he i hi ((boundary_iff_slack hh x hl i).mpr ht))) (hx i)
  exact ⟨fixed 0 (by decide),fixed 2 (by decide),fixed 4 (by decide)⟩

theorem three_dimers_amplitude {h : ℝ} {x : Fin 6 → ℝ} (hh : 0 ≤ h)
    (h0 : gap positiveSix x 0 = h) (h2 : gap positiveSix x 2 = h) (h4 : gap positiveSix x 4 = h) :
    ‖structureFactor x 1‖ ≤ 3*(2*π*h) := by
  rw [gap_interior _ _ _ (by decide)] at h0 h2 h4
  change x 1-x 0 = h at h0
  change x 3-x 2 = h at h2
  change x 5-x 4 = h at h4
  have hb (a b : ℝ) (hg : b-a=h) : ‖wave 1 a-wave 1 b‖ ≤ 2*π*h := by
    have := wave_chord_le 1 a b
    rwa [abs_sub_comm,hg,abs_of_nonneg hh,Nat.cast_one,mul_one] at this
  rw [sixWave_eq,sixWave]
  rw [show wave 1 (x 0)-wave 1 (x 1)+wave 1 (x 2)-wave 1 (x 3)+wave 1 (x 4)-wave 1 (x 5)
      = ((wave 1 (x 0)-wave 1 (x 1))+(wave 1 (x 2)-wave 1 (x 3)))+
        (wave 1 (x 4)-wave 1 (x 5)) by ring]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  linarith only [hb _ _ h0,hb _ _ h2,hb _ _ h4]

/-- At the larger narrow-strip floors the 4+2 and 2+2+2 cases are also
impossible by the actual midpoint spacings, even across the wrapping gap. -/
theorem even_arcs_impossible {x : Fin 6 → ℝ} {h d : ℝ} (hh : 0 ≤ h)
    (hx : Feasible positiveSix h x) (A : Support) (hA : A={1} ∨ A={1,3})
    (hd : d < π/2) (hwide : 2*d < 3*(2*π*h)) (hn : InPeakArcs x h A d) : False := by
  let η := 2*π*h
  have hη : 0 ≤ η := by dsimp [η]; positivity
  rcases hA with rfl|rfl
  · let A : Support := {1}
    let u := blockMid x h A
    obtain ⟨i,hi⟩ := hn 0 (by decide)
    obtain ⟨j,hj⟩ := hn 1 (by decide)
    have hs0 := mid_step hx A 0 (by decide)
    have hs1 := mid_step hx A 1 (by decide)
    have hclose : u 2=u 0+2*π := mid_close x h A
    have t0 : lengthLift A 0 = 2 := by decide
    have t1 : lengthLift A 1 = 4 := by decide
    have t2 : lengthLift A 2 = 2 := by decide
    change ((lengthLift A 0:ℝ)+(lengthLift A 1:ℝ))*η/2 ≤ u 1-u 0 at hs0
    change ((lengthLift A 1:ℝ)+(lengthLift A 2:ℝ))*η/2 ≤ u 2-u 1 at hs1
    rw [t0,t1] at hs0
    rw [t1,t2,hclose] at hs1
    rw [show peakIndex ({1}:Support) 0 = 1 by decide,Nat.cast_one] at hi
    rw [show peakIndex ({1}:Support) 1 = 1 by decide,Nat.cast_one] at hj
    change |u 0-((1:ℝ)*(π/2)+2*π*(i:ℝ))| ≤ d at hi
    change |u 1-((1:ℝ)*(π/2)+2*π*(j:ℝ))| ≤ d at hj
    exact exclude_even_four_two hd hwide hη (by norm_num at hs0; linarith)
      (by norm_num at hs1; linarith) hi hj
  · let A : Support := {1,3}
    let u := blockMid x h A
    obtain ⟨i,hi⟩ := hn 0 (by decide)
    obtain ⟨j,hj⟩ := hn 1 (by decide)
    obtain ⟨k,hk⟩ := hn 2 (by decide)
    have step (m : ℕ) (hm : m<3) : 2*η ≤ u (m+1)-u m := by
      have H := mid_step hx A m hm
      have tl : ∀ n : Fin 4, lengthLift A n=2 := by decide
      have tm := tl ⟨m,by omega⟩
      have tm' := tl ⟨m+1,by omega⟩
      change lengthLift A m = 2 at tm
      change lengthLift A (m+1) = 2 at tm'
      rw [tm,tm'] at H
      change ((2:ℝ)+2)*η/2 ≤ _ at H
      linarith
    have H := step 2 (by decide)
    change 2*η ≤ u 3-u 2 at H
    rw [show u 3=u 0+2*π from mid_close x h A] at H
    rw [show peakIndex ({1,3}:Support) 0 = 1 by decide,Nat.cast_one] at hi
    rw [show peakIndex ({1,3}:Support) 1 = 1 by decide,Nat.cast_one] at hj
    rw [show peakIndex ({1,3}:Support) 2 = 1 by decide,Nat.cast_one] at hk
    change |u 0-((1:ℝ)*(π/2)+2*π*(i:ℝ))| ≤ d at hi
    change |u 1-((1:ℝ)*(π/2)+2*π*(j:ℝ))| ≤ d at hj
    change |u 2-((1:ℝ)*(π/2)+2*π*(k:ℝ))| ≤ d at hk
    exact exclude_even_three_dimers hd (by linarith : 2*d < 4*η) hη (step 0 (by decide))
      (step 1 (by decide)) H hi hj hk

end GaussianChains.Strip
