import ClustersSelectionGeometry
import ClustersSelectionKernel
import ClustersWidthPhysical

/-! Applying the angular two-block expansion to actual cyclic labels in the
period-normalized image energy. The two inputs are arbitrary angular offsets
from zero and π, in the order in which those blocks are visited. -/
noncomputable section
open Real Finset
namespace GaussianChains.Clusters

theorem joined_angularScore (k l : ℕ) (q : ℝ)
    (x : Fin (2*k+1) → ℝ) (y : Fin (2*l+1) → ℝ) :
    angularScore q (joinedBlocks x y) =
      blockSum charge charge x x (angularK q) 0 +
      blockSum charge charge y y (angularK q) 0 -
      2*blockSum charge charge x y (angularK q) π := by
  let X := joinedBlocks x y
  let ang := Fin.append x (fun j => π+y j)
  let H (i j : Fin ((2*k+1)+(2*l+1))) :=
    charge i*charge j*angularK q (2*π*(X j-X i))
  have ht (i j) : 2*π*(X j-X i) = ang j - ang i := by
    dsimp [X,joinedBlocks,ang]
    field_simp [pi_ne_zero] <;> ring
  have hl (i : Fin (2*k+1)) : charge (i.castAdd (2*l+1)) = charge i := rfl
  have hr (j : Fin (2*l+1)) : charge (Fin.natAdd (2*k+1) j) = -charge j := by
    simp [charge, pow_add, pow_mul]
  have hneg (z : ℝ) : angularK q (-z) = angularK q z := angularCos_even 0 q z
  have href (z : ℝ) : angularK q (π-z) = angularK q (π+z) := angularCos_pi_reflect 0 q z
  have AA (i j : Fin (2*k+1)) : H (i.castAdd (2*l+1)) (j.castAdd (2*l+1)) =
      charge i*charge j*angularK q (x i-x j) := by
    dsimp only [H]
    rw [ht,hl,hl]
    simp only [ang,Fin.append_left]
    rw [← neg_sub (x i) (x j), hneg]
  have BB (i j : Fin (2*l+1)) : H (Fin.natAdd (2*k+1) i) (Fin.natAdd (2*k+1) j) =
      charge i*charge j*angularK q (y i-y j) := by
    dsimp only [H]
    rw [ht,hr,hr]
    simp only [ang,Fin.append_right,add_sub_add_left_eq_sub,neg_mul_neg]
    rw [← neg_sub (y i) (y j), hneg]
  let XY (i : Fin (2*k+1)) (j : Fin (2*l+1)) :=
    charge i*charge j*angularK q (π+(x i-y j))
  have AB (i : Fin (2*k+1)) (j : Fin (2*l+1)) :
      H (i.castAdd (2*l+1)) (Fin.natAdd (2*k+1) j) = -XY i j := by
    dsimp only [H,XY]
    rw [ht,hl,hr]
    simp only [ang,Fin.append_left,Fin.append_right]
    rw [show π+y j-x i = π-(x i-y j) by ring,href]
    ring
  have BA (i : Fin (2*k+1)) (j : Fin (2*l+1)) :
      H (Fin.natAdd (2*k+1) j) (i.castAdd (2*l+1)) = -XY i j := by
    dsimp only [H,XY]
    rw [ht,hl,hr]
    simp only [ang,Fin.append_left,Fin.append_right]
    rw [show x i-(π+y j) = -(π-(x i-y j)) by ring, hneg, href]
    ring
  change (∑ i, ∑ j, H i j) = _
  have row (i) : (∑ j, H i j) =
      (∑ j : Fin (2*k+1), H i (j.castAdd (2*l+1))) + (∑ j : Fin (2*l+1), H i (Fin.natAdd (2*k+1) j)) :=
    Fin.sum_univ_add _
  rw [Fin.sum_univ_add (fun i => ∑ j, H i j)]
  simp_rw [row,AA,BB,AB,BA]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun j i => XY i j)]
  simp only [blockSum,zero_add,XY]
  ring

theorem odd_charge_sum (k : ℕ) : ∑ i : Fin (2*k+1), charge i = 1 := by
  unfold charge
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i),sum_range_succ]
  have hz : ∑ i ∈ range (2*k), (-1:ℝ)^i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i)]
    exact charge_sum_even k
  simp [hz,pow_mul]

/-- Equation (5) with the deficit stated in terms of the physical period-one
image energy, for every localized pair of odd blocks with the actual charges. -/
theorem imageEnergy_joined_taylor (k l : ℕ) (x : Fin (2*k+1) → ℝ) (y : Fin (2*l+1) → ℝ)
    {s C η : ℝ} (hs : 0<s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hx : ∀ i, |x i| ≤ C*η) (hy : ∀ j, |y j| ≤ C*η) :
    let N : ℝ := (((2*k+1)+(2*l+1) : ℕ):ℝ)
    let c := sqrt (π/s)
    let q := exp (-(π^2)/s)
    let P₀ := ∑ i, charge i*x i
    let Pπ := ∑ j, charge j*y j
    let V₀ := (∑ i, charge i*(x i)^2)-P₀^2
    let Vπ := (∑ i, charge i*(y i)^2)-Pπ^2
    let I := 1-2*(kernel s 0-kernel s (1/2))/N
    let D := angularCos 2 q 0-angularCos 2 q π
    |N*(imageEnergy s (joinedBlocks x y)-I)/(2*c*q) -
        (D*(V₀+Vπ) - angularCos 2 q π*(P₀-Pπ)^2)| ≤ 4/3*N^2*C^4*η^4 := by
  let q := exp (-(π^2)/s)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos pi_pos)) hs)
  have habs {n : ℕ} (i : Fin n) : |charge i| = 1 := by simp [charge, abs_pow]
  have hg := gaussian_two_block_taylor charge charge x y (odd_charge_sum k) (odd_charge_sum l)
    habs habs (exp_pos _).le hq hR hx hy
  have hf {n : ℕ} (hn : 0 < n) (he : ∃ m, n = 2*m) (X : Fin n → ℝ) :
      (n:ℝ)*(imageEnergy s X-(1-2*(kernel s 0-kernel s (1/2))/(n:ℝ)))/
        (2*sqrt (π/s)*q) =
      2*(angularK q 0-angularK q π)-angularScore q X := by
    obtain ⟨m,rfl⟩ := he
    exact angular_deficit_eq m (by omega) hs X
  dsimp only
  rw [hf (by omega) ⟨k+l+1,by omega⟩,joined_angularScore]
  dsimp only at hg
  simp only [Fintype.card_fin] at hg
  convert hg using 1
  · apply congrArg abs
    ring
  · push_cast
    <;> ring

#print axioms imageEnergy_joined_taylor
end GaussianChains.Clusters

