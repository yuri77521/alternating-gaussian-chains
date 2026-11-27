import StripFaceReduction
import ChainMinimum
import ChainSymmetry

/-! Sound reduction from the entire feasible simplex to the eighteen support
representatives. Reflection is used only to discharge off-edge supports:
the resulting face representative is a *cyclic shift* of the original cell. -/
noncomputable section
namespace GaussianChains.Strip
abbrev positiveSix : 0 < 6 := by decide

def labelledSupport (h : ℝ) (x : Fin 6 → ℝ) :=
  activeSupport (slack h (gap positiveSix x))

def largestLast (x : Fin 6 → ℝ) := ∀ i, gap positiveSix x i ≤ gap positiveSix x 5

def chamberReflect (x : Fin 6 → ℝ) := shiftLifts positiveSix (reflectLifts positiveSix x) 1

theorem ground_shift {h s : ℝ} {x : Fin 6 → ℝ} (hx : IsGroundState positiveSix h s x) (k : Fin 6) :
    IsGroundState positiveSix h s (shiftLifts positiveSix x k) := by
  refine ⟨(feasible_shiftLifts_iff _ _ _ _).mpr hx.1, fun y hy => ?_⟩
  rw [imageEnergy_shiftLifts _ (by decide)]
  exact hx.2 y hy

theorem ground_chamberReflect {h s : ℝ} {x : Fin 6 → ℝ} (hx : IsGroundState positiveSix h s x) :
    IsGroundState positiveSix h s (chamberReflect x) := by
  apply ground_shift
  refine ⟨(feasible_reflectLifts_iff _ _ _).mpr hx.1, fun y hy => ?_⟩
  rw [imageEnergy_reflectLifts _ (by decide)]
  exact hx.2 y hy

theorem largest_chamberReflect {x : Fin 6 → ℝ} (hx : largestLast x) :
    largestLast (chamberReflect x) := by
  intro i
  simp only [chamberReflect,gap_shiftLifts,gap_reflectLifts]
  exact hx _

theorem support_chamberReflect (h : ℝ) (x : Fin 6 → ℝ) :
    labelledSupport h (chamberReflect x) = reflectSupport (labelledSupport h x) := by
  have idrev (i : Fin 5) : (i.castSucc + (1:Fin 6)).rev = i.rev.castSucc := by fin_cases i <;> rfl
  ext i
  simp only [labelledSupport,reflectSupport,Finset.mem_image,mem_active_iff,slack,
    chamberReflect,gap_shiftLifts,gap_reflectLifts,idrev]
  constructor
  · intro hi
    exact ⟨i.rev,hi,Fin.rev_rev i⟩
  · rintro ⟨j,hj,rfl⟩
    simpa only [Fin.rev_rev] using hj

/-- It suffices to rule out the eighteen actual supports in the largest-last
chamber. No unique largest gap or positive free-coordinate margin is assumed. -/
theorem full_domain_from_support_exclusion {s h : ℝ} (hh : h < 1/6)
    (exclude : ∀ x : Fin 6 → ℝ, IsGroundState positiveSix h s x → largestLast x →
      labelledSupport h x ∉ offEdgeReps)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) :
    ∃ k : Fin 6, ∃ t : ℝ, PackedFace.feasible h t ∧
      ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + PackedFace.sites h t i := by
  obtain ⟨j,hj⟩ := exists_distinguished (gap positiveSix x)
  let k : Fin 6 := j+1
  let y := shiftLifts positiveSix x k
  have hy := ground_shift hx k
  have hmax : largestLast y := by
    intro i
    have he : (5:Fin 6)+k = j := by dsimp [k]; fin_cases j <;> rfl
    simpa only [y,gap_shiftLifts,he] using hj (i+k)
  have hcanonical := exclude y hy hmax
  have href := exclude (chamberReflect y) (ground_chamberReflect hy) (largest_chamberReflect hmax)
  rw [support_chamberReflect] at href
  have hedge : labelledSupport h y = ∅ ∨ labelledSupport h y = {2} := by
    rcases supports_exhaustive (labelledSupport h y) with h₀|h₂|hC|hR
    · exact Or.inl h₀
    · exact Or.inr h₂
    · exact False.elim (hcanonical hC)
    · exact False.elim (href hR)
  exact ⟨k, active_support_face hh hy.1 hedge⟩

#print axioms full_domain_from_support_exclusion
end GaussianChains.Strip
