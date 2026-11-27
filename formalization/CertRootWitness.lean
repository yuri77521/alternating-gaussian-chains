import CertRootValue
import CertRootWitnessData
import ChainMinimum

/-! Real-space verification of the two rational competitors used at width 22.
The statements compare energies of explicit cells; no global-optimality
assumption is used. -/

namespace GaussianChains.Root22

theorem witnessX_feasible : Feasible (by decide) (1/1000) (fun i => (witnessX i : ℝ)) := by
  intro i
  fin_cases i <;> norm_num [gap,liftSite,witnessX]

theorem witnessZ_feasible : Feasible (by decide) (1/1000) (fun i => (witnessZ i : ℝ)) := by
  intro i
  fin_cases i <;> norm_num [gap,liftSite,witnessZ]

private theorem witness_mem {v : Fin 6 → ℚ} (h : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    Encloses (energyBox (witnessBoxes v)) (imageEnergy 22 fun i => (v i : ℝ)) := by
  apply energyBox_sound (coords := witnessBoxes v) (x := fun i => (v i:ℝ))
    (fun i => ⟨le_rfl, le_rfl⟩)
  intro i j
  have hi : 0 ≤ (v i:ℝ) ∧ (v i:ℝ) ≤ 1 := by exact_mod_cast h i
  have hj : 0 ≤ (v j:ℝ) ∧ (v j:ℝ) ≤ 1 := by exact_mod_cast h j
  exact abs_le.mpr ⟨by linarith [hi.2,hj.1], by linarith [hi.1,hj.2]⟩

theorem witnessX_enclosed :
    6671068104073566285/10^19 < imageEnergy 22 (fun i => (witnessX i : ℝ)) ∧
      imageEnergy 22 (fun i => (witnessX i : ℝ)) < 6671068104073566286/10^19 := by
  have h := witness_mem (v := witnessX) (by intro i; fin_cases i <;> norm_num [witnessX])
  have lo := (Rat.cast_lt (K := ℝ)).mpr evalX.1
  have hi := (Rat.cast_lt (K := ℝ)).mpr evalX.2
  push_cast at lo hi
  exact ⟨lo.trans_le h.1,h.2.trans_lt hi⟩

theorem witnessZ_enclosed :
    6650358445233044362/10^19 < imageEnergy 22 (fun i => (witnessZ i : ℝ)) ∧
      imageEnergy 22 (fun i => (witnessZ i : ℝ)) < 6650358445233044363/10^19 := by
  have h := witness_mem (v := witnessZ) (by intro i; fin_cases i <;> norm_num [witnessZ])
  have lo := (Rat.cast_lt (K := ℝ)).mpr evalZ.1
  have hi := (Rat.cast_lt (K := ℝ)).mpr evalZ.2
  push_cast at lo hi
  exact ⟨lo.trans_le h.1,h.2.trans_lt hi⟩

theorem witnessX_minus_Z :
    (0.00207096588405:ℝ) <
      imageEnergy 22 (fun i => (witnessX i : ℝ)) - imageEnergy 22 (fun i => (witnessZ i : ℝ)) := by
  linarith [witnessX_enclosed.1, witnessZ_enclosed.2]

theorem witnessX_minus_reflection {r : ℝ} (hr : (lowerRoot:ℝ) ≤ r ∧ r ≤ (upperRoot:ℝ)) :
    (0.00207096589396576:ℝ) <
      imageEnergy 22 (fun i => (witnessX i : ℝ)) - imageEnergy 22 (reflectedSites r) := by
  have hh := (reflection_energy_enclosed hr).2
  norm_num [energyUpper] at hh
  linarith [witnessX_enclosed.1]

/-- Moving just the fourth site produces a feasible configuration belonging
only to the omitted child, with the translation gauge fixed. -/
theorem removed_child_contains_feasible :
    ∃ x : Fin 6 → ℝ, Feasible (by decide) (1/1000) x ∧
      (nearX.Right 3 (witnessX 3)).Mem x ∧ ¬(nearX.Left 3 (witnessX 3)).Mem x := by
  let v : Fin 6 → ℚ := ![0,1/8,63/500,500001/2000000,1/2,3/4]
  let x := fun i => (v i:ℝ)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x,v,gap,liftSite]
  · have checked : ∀ i, ((nearX.Right 3 (witnessX 3)) i).lo ≤ v i ∧
        v i ≤ ((nearX.Right 3 (witnessX 3)) i).hi := by
      dsimp only [v]
      decide +kernel
    intro i
    exact ⟨Rat.cast_le.mpr (checked i).1,Rat.cast_le.mpr (checked i).2⟩
  · intro hm
    have checked : ((nearX.Left 3 (witnessX 3)) 3).hi < v 3 := by
      dsimp only [v]
      decide +kernel
    exact (not_le_of_gt (Rat.cast_lt.mpr checked)) (hm 3).2

theorem witnessX_mem_nearX : nearX.Mem (fun i => (witnessX i : ℝ)) := by
  intro i
  change ((witnessX i-1/10^6:ℚ):ℝ) ≤ (witnessX i:ℝ) ∧
    (witnessX i:ℝ) ≤ ((witnessX i+1/10^6:ℚ):ℝ)
  push_cast
  constructor <;> linarith

private theorem nearX_span {x : Fin 6 → ℝ} (hx : nearX.Mem x) :
    ∀ i j, |x j-x i| ≤ 1 := by
  have hbox (i : Fin 6) : (-1/1000:ℝ) ≤ x i ∧ x i ≤ 751/1000 := by
    have hl := (hx i).1
    have hu := (hx i).2
    simp only [nearX, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat] at hl hu
    have hw : (0:ℝ) ≤ (witnessX i:ℝ) ∧ (witnessX i:ℝ) ≤ 3/4 := by
      fin_cases i <;> norm_num [witnessX]
    constructor <;> linarith [hw.1,hw.2]
  exact fun i j => abs_le.mpr
    ⟨by linarith [(hbox i).2,(hbox j).1], by linarith [(hbox i).1,(hbox j).2]⟩

private theorem trialScoreBox_sound {b : GaussianChains.Cert.Box 6} {x : Fin 6 → ℝ}
    (hx : b.Mem x) (hspan : ∀ i j, |x j-x i| ≤ 1) :
    (trialScoreBox b).Mem
      (imageEnergy 22 (fun i => (witnessZ i:ℝ)) - imageEnergy 22 x) := by
  have he := energyBox_sound (coords := fun i => ((b i).lo,(b i).hi)) (x := x)
    (fun i => hx i) hspan
  have hz := witness_mem (v := witnessZ) (by intro i; fin_cases i <;> norm_num [witnessZ])
  exact subBox_sound hz he

/-- Every point in this closed box loses to the feasible rational cell Z,
including the feasible center X and the collision-free points around it. -/
theorem nearX_excluded {x : Fin 6 → ℝ} (hx : nearX.Mem x) :
    imageEnergy 22 (fun i => (witnessZ i : ℝ)) < imageEnergy 22 x :=
  GaussianChains.Cert.score_leaf_excludes nearX_accepted (trialScoreBox_sound hx (nearX_span hx)).2

private noncomputable def trialValue (x : Fin 6 → ℝ) : GaussianChains.Cert.Quantity → ℝ
  | .score _ => imageEnergy 22 (fun i => (witnessZ i:ℝ)) - imageEnergy 22 x
  | _ => 0

theorem nearX_no_ground_state {x : Fin 6 → ℝ} (hx : nearX.Mem x) :
    ¬IsGroundState (by decide) (1/1000) 22 x := by
  let candidate := fun y : Fin 6 → ℝ =>
    IsGroundState (by decide) (1/1000) 22 y ∧ ∀ i j, |y j-y i| ≤ 1
  have encl : ∀ b y, GaussianChains.Cert.Box.Mem b y → candidate y → ∀ k,
      (trialOracle b k).Mem (trialValue y k) := by
    intro b y hy hc k
    cases k with
    | score n => exact trialScoreBox_sound hy hc.2
    | feasible n | gradient n | curvature n => exact ⟨by simp [trialOracle,trialValue], by simp [trialOracle,trialValue]⟩
  have nec : ∀ y, candidate y → ∀ k, GaussianChains.Cert.Necessary k (trialValue y k) := by
    intro y hc k
    cases k with
    | score n => exact sub_nonneg.mpr (hc.1.2 _ witnessZ_feasible)
    | feasible n | gradient n | curvature n => simp [GaussianChains.Cert.Necessary,trialValue]
  intro hg
  exact GaussianChains.Cert.accept_sound (target := none) encl nec nearXSplit nearX
    nearX_split_accepted hx ⟨hg,nearX_span hx⟩

#print axioms witnessX_minus_Z
#print axioms witnessX_minus_reflection
#print axioms nearX_excluded
#print axioms nearX_no_ground_state
end GaussianChains.Root22
