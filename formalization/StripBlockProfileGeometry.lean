import StripPackedBlocks
import StripBlockProfileModes
import ChainFourier

/-! Change of the structure factor under translation of one actual maximal block. -/

noncomputable section
namespace GaussianChains.Strip
open Real ClusterSeries

theorem phase_add_angles (u v : ℝ) : phase (u+v) = phase u * phase v := by
  simp [phase, add_mul, Complex.exp_add]

def stripSiteMode (x : Fin 6 → ℝ) (n j : ℕ) : ℂ :=
  (-1 : ℂ)^j * phase (2*π*(n:ℝ)*liftSite positiveSix x j)

theorem structureFactor_eq_six_modes (x : Fin 6 → ℝ) (n : ℕ) :
    structureFactor x n = ∑ j ∈ Finset.range 6, stripSiteMode x n j := by
  rw [← Fin.sum_univ_eq_sum_range (stripSiteMode x n)]
  unfold structureFactor
  apply Finset.sum_congr rfl
  intro i _
  simp [stripSiteMode,charge,liftSite_fin,phase]

private theorem sum_packed_interval (a b : ℕ) (hab : a+b ≤ 6) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range 6, if a ≤ j ∧ j < a+b then f j else 0) =
      ∑ j ∈ Finset.range b, f (a+j) := by
  let g (j : ℕ) := if a ≤ j ∧ j < a+b then f j else 0
  change ∑ j ∈ Finset.range 6, g j = _
  rw [show 6 = (a+b)+(6-(a+b)) by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hlow : ∑ j ∈ Finset.range a, g j = 0 := Finset.sum_eq_zero fun j hj => by
    simp [g, not_le.mpr (Finset.mem_range.mp hj)]
  have hhigh : ∑ j ∈ Finset.range (6-(a+b)), g (a+b+j) = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [g, show ¬a+b+j < a+b by omega]
  rw [hlow, hhigh, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [g, Finset.mem_range.mp hj]

def blockModeSum (x : Fin 6 → ℝ) (A : Support) (k : Fin 6) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (blockLength A k), stripSiteMode x n (blockStart A k+j)

/-- The displacement u is angular; the physical shift of each moved site
in the unit-period chart is u/(2π). All untouched labels cancel. -/
theorem block_structure_delta (x : Fin 6 → ℝ) (A : Support) (k : Fin 6)
    (hk : k.val < (blocks A).length) (n : ℕ) (u : ℝ) :
    structureFactor (shiftBlock x A k (u/(2*π))) n - structureFactor x n =
      (phase ((n:ℝ)*u) - 1) * blockModeSum x A k n := by
  let a := blockStart A k
  let b := blockLength A k
  have hab : a+b ≤ 6 := (block_bounds A k hk).2
  rw [structureFactor_eq_six_modes,structureFactor_eq_six_modes,← Finset.sum_sub_distrib]
  calc
    _ = ∑ j ∈ Finset.range 6, if a ≤ j ∧ j < a+b then
        (phase ((n:ℝ)*u)-1)*stripSiteMode x n j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      let i : Fin 6 := ⟨j,Finset.mem_range.mp hj⟩
      have hy := liftSite_fin positiveSix (shiftBlock x A k (u/(2*π))) i
      have hx := liftSite_fin positiveSix x i
      change liftSite _ _ j = _ at hy hx
      by_cases hm : a ≤ j ∧ j < a+b
      · have hmod : inBlock A k i := hm
        simp only [if_pos hm,stripSiteMode,hy,hx,shiftBlock,blockSpeed,if_pos hmod,
          Int.cast_one,mul_one]
        rw [show 2*π*(n:ℝ)*(x i+u/(2*π)) = 2*π*(n:ℝ)*x i+(n:ℝ)*u by
          field_simp [pi_ne_zero] <;> ring, phase_add_angles]
        ring
      · have hmod : ¬ inBlock A k i := hm
        simp only [if_neg hm,stripSiteMode,hy,hx,shiftBlock,blockSpeed,if_neg hmod,
          Int.cast_zero,mul_zero,add_zero,sub_self]
    _ = _ := by
      rw [sum_packed_interval a b hab,blockModeSum,Finset.mul_sum]

/-- Middle of a block with b+1 sites; it is the angular argument of the
frozen one-dimensional profile. -/
def blockCenter (x : Fin 6 → ℝ) (a : ℕ) (b : Fin 4) (h : ℝ) : ℝ :=
  2*π*(liftSite positiveSix x a + (b.val:ℝ)*h/2)

theorem blockModeSum_centered {x : Fin 6 → ℝ} {h : ℝ} (hh : h < 1/6)
    (hx : Feasible positiveSix h x) (hlast : largestLast x) (k : Fin 6)
    (hk : k.val < (blocks (labelledSupport h x)).length) (b : Fin 4)
    (hlen : blockLength (labelledSupport h x) k = b.val+1) (n : ℕ) :
    let A := labelledSupport h x
    let a := blockStart A k
    blockModeSum x A k n =
      ((-1:ℂ)^a * phase ((n:ℝ)*blockCenter x a b h)) *
        centeredModeSum b ((n:ℝ)*(2*π*h)) := by
  dsimp only
  unfold blockModeSum centeredModeSum
  rw [hlen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let a := blockStart (labelledSupport h x) k
  have hj' : j < blockLength (labelledSupport h x) k := by
    rw [hlen]
    exact Finset.mem_range.mp hj
  have hxj := block_progression hh hx hlast k hk j hj'
  change liftSite positiveSix x (a+j) = liftSite positiveSix x a + (j:ℝ)*h at hxj
  change (-1:ℂ)^(a+j) * phase (2*π*(n:ℝ)*liftSite positiveSix x (a+j)) = _
  rw [hxj,pow_add]
  rw [show 2*π*(n:ℝ)*(liftSite positiveSix x a+(j:ℝ)*h) =
    (n:ℝ)*blockCenter x a b h + ((j:ℝ)-(b.val:ℝ)/2)*((n:ℝ)*(2*π*h)) by
      unfold blockCenter; ring,phase_add_angles]
  dsimp only [a]
  ring

end GaussianChains.Strip
