import PackedFaceGapLink
import ChainSymmetry

/-! The two displacements in each pair have the same species under reflection.
Switching which triple is first, by contrast, is a three-label cyclic shift. -/
namespace GaussianChains.PackedFace

theorem reflect_sites (h t : ℝ) :
    sites h (-t) = fun i =>
      reflectLifts (by decide) (shiftLifts (by decide) (sites h t) 2) i + (1+2*h) := by
  funext i
  fin_cases i <;> norm_num [reflectLifts,shiftLifts,liftSite,sites,Matrix.cons_val_succ] <;> ring

theorem reflected_labels_preserve_species (i : Fin 6) : charge (2-i) = charge i := by
  rw [sub_eq_add_neg,charge_cyclic_add (by decide), charge_reverse (by decide)]
  have h : charge (2:Fin 6) = 1 := by norm_num [charge]
  rw [h,one_mul]

theorem swapping_triples_reverses_species (i : Fin 6) : charge (i+3) = -charge i := by
  rw [charge_cyclic_add (by decide)]
  have h : charge (3:Fin 6) = -1 := by norm_num [charge]
  rw [h,mul_neg_one]

theorem swap_triples_sites (h t : ℝ) :
    sites h (-t) = fun i => shiftLifts (by decide) (sites h t) 3 i - (1/2+t) := by
  funext i
  fin_cases i <;> norm_num [shiftLifts,liftSite,sites,Matrix.cons_val_succ] <;> ring

end GaussianChains.PackedFace

