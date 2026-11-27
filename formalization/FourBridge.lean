import ChainEnergy
import GaussianDisplacementEnergy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! # Literal four-site bridge to the upstream displacement theorem

The upstream prime on the image sum identifies the central self-term by
coordinate equality. Injectivity is the hypothesis that makes this agree
with omission by label in the physical energy.
-/

namespace GaussianChains

open AlternatingChains.Fourier
open scoped BigOperators

noncomputable section

/-- Period-four physical coordinates, before dividing by the period. -/
def fourSites (b d : ℝ) (i : Fin 4) : ℝ :=
  if i = 0 then 0 else if i = 1 then b else if i = 2 then 2 else d

theorem fourSites_injective (b d : ℝ) (hb : 0 < b) (hb₂ : b < 2) (hd : 2 < d) :
    Function.Injective (fourSites b d) := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact hb
  · exact hb₂
  · exact hd

private theorem four_ordered_pairs (b d : ℝ) (f : ℝ → ℝ → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, charge i * charge j * f (fourSites b d j) (fourSites b d i)) =
      signedCell b d (fun x => signedCell b d (f x)) := by
  simp only [Fin.sum_univ_four, show fourSites b d 0 = 0 from rfl,
    show fourSites b d 1 = b from rfl, show fourSites b d 2 = 2 from rfl,
    show fourSites b d 3 = d from rfl]
  norm_num [charge, signedCell]
  ring

/-- Equality of the two literal ordered, prime image sums. Reindexing the two
finite labels accounts for the upstream convention `x - y`. -/
theorem physicalEnergy_four_eq_cellEnergyAt (a b d : ℝ)
    (hinj : Function.Injective (fourSites b d)) :
    physicalEnergy a 4 (fourSites b d) = cellEnergyAt a b d := by
  let f (x y : ℝ) := ∑' k : ℤ, if x-y = 0 ∧ k = 0 then 0
    else Real.exp (-a * (x-y + 4*(k:ℝ))^2)
  have term (i j : Fin 4) :
      (∑' k : ℤ, if i = j ∧ k = 0 then 0
        else Real.exp (-a * (fourSites b d j - fourSites b d i + 4*(k:ℝ))^2)) =
        f (fourSites b d j) (fourSites b d i) := by
    unfold f
    simp only [sub_eq_zero, hinj.eq_iff]
    simp only [show j = i ↔ i = j from eq_comm]
  unfold physicalEnergy primedImage cellEnergyAt
  simp_rw [term]
  rw [four_ordered_pairs]
  rfl

theorem physicalEnergy_four_quarter (b d : ℝ) (hinj : Function.Injective (fourSites b d)) :
    physicalEnergy (1/4) 4 (fourSites b d) = cellEnergy b d :=
  (physicalEnergy_four_eq_cellEnergyAt (1/4) b d hinj).trans (cellEnergyAt_quarter b d)

/-- At the collision-closure cell (0,0,2,2) the two conventions do give
different answers. The physical prime removes four central label self-pairs;
the upstream prime also removes the coincident opposite-label interactions. -/
theorem four_collision_conventions (a : ℝ) (ha : 0 < a) :
    physicalEnergy a 4 (fourSites 0 2) = 1 ∧ cellEnergyAt a 0 2 = 0 := by
  constructor
  · rw [physicalEnergy_eq_imageEnergy (N := 4) (by decide) a 4 ha (by norm_num)]
    unfold imageEnergy
    rw [four_ordered_pairs 0 2 (fun x y => kernel (a*4^2) (x/4-y/4))]
    simp [signedCell]
  · simp [cellEnergyAt, signedCell]

/-- Normalized equation (2) at period four has width `16*a`. -/
theorem imageEnergy_four_eq_cellEnergyAt (a b d : ℝ) (ha : 0 < a)
    (hinj : Function.Injective (fourSites b d)) :
    imageEnergy (16*a) (fun i => fourSites b d i / 4) = cellEnergyAt a b d := by
  have he := physicalEnergy_eq_imageEnergy (N := 4) (by decide) a 4 ha (by norm_num)
    (fourSites b d)
  rw [show a * (4:ℝ)^2 = 16*a by ring] at he
  exact he.symm.trans (physicalEnergy_four_eq_cellEnergyAt a b d hinj)

theorem imageEnergy_four_quarter (b d : ℝ) (hinj : Function.Injective (fourSites b d)) :
    imageEnergy 4 (fun i => fourSites b d i / 4) = cellEnergy b d := by
  have he := imageEnergy_four_eq_cellEnergyAt (1/4) b d (by norm_num) hinj
  norm_num at he
  exact he.trans (cellEnergyAt_quarter b d)

/-- Proposition 2 of upstream PR 7, transported to the general normalized
energy. The displacement `u` is in physical units at period four. -/
theorem imageEnergy_four_displacement_lt (a u : ℝ) (ha : 0 < a)
    (hq : gaussianNome a ≤ 1/4) (hu₀ : 0 < |u|) (hu₁ : |u| < 1) :
    imageEnergy (16*a) (fun i => fourSites (1+u) (3-u) i / 4) <
      imageEnergy (16*a) (fun i => fourSites 1 3 i / 4) := by
  obtain ⟨hb, hb₂, hd, _⟩ := displacement_ordered u hu₁
  rw [imageEnergy_four_eq_cellEnergyAt _ _ _ ha (fourSites_injective _ _ hb hb₂ hd),
    imageEnergy_four_eq_cellEnergyAt _ _ _ ha
      (fourSites_injective 1 3 (by norm_num) (by norm_num) (by norm_num))]
  exact displacement_energy_lt a u ha hq hu₀ hu₁

end
end GaussianChains
