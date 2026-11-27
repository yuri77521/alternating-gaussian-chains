import ClusterSeriesEnergy
import PackedFaceModesEnergy
import StripFiveOnePowers
import ClustersTwo
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! All placements of the singleton relative to a packed five-site block.
The first five angles are −2η,−η,0,η,2η and the sixth is π+v. -/
noncomputable section
namespace GaussianChains.Strip
open Real
open ClusterSeries

def fiveSites (h t : ℝ) (j : Fin 6) : ℝ :=
  if j = 5 then 1/2+t else packedSites 2 0 h j

theorem fiveSites_coordinates (h t : ℝ) :
    fiveSites h t = ![-2*h,-h,0,h,2*h,1/2+t] := by
  ext j
  fin_cases j <;> norm_num [fiveSites,packedSites,packedAngle,Matrix.cons_val,Fin.ext_iff] <;>
    field_simp [pi_ne_zero] <;> ring

private theorem exp_half_add (n : ℕ) (t : ℝ) :
    PackedFace.wave n (1/2+t) =
      (((-1:ℝ)^n : ℝ):ℂ)*PackedFace.wave n t := by
  unfold PackedFace.wave
  rw [show 2*π*(n:ℝ)*(1/2+t) = (n:ℝ)*π + 2*π*n*t by ring]
  push_cast
  rw [add_mul, Complex.exp_add, mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem packed_last (h : ℝ) : packedSites 2 0 h (5 : Fin 6) = 1/2 := by
  norm_num [packedSites,packedAngle] <;> field_simp [pi_ne_zero]

private theorem block_two (w : ℝ) : block 2 w = five w := by
  norm_num [block, five]
  ring

theorem structureFactor_fiveSites (n : ℕ) (h t : ℝ) :
    structureFactor (fiveSites h t) n =
      (five (n*(2*π*h)) : ℂ) - (((-1:ℝ)^n:ℝ):ℂ) * PackedFace.wave n t := by
  have hd : structureFactor (fiveSites h t) n - structureFactor (packedSites 2 0 h) n =
      -(PackedFace.wave n (1/2+t) - PackedFace.wave n (1/2)) := by
    unfold structureFactor
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (5:Fin 6)]
    · change (charge (5 : Fin 6):ℂ) * PackedFace.wave n (fiveSites h t 5) -
        (charge (5 : Fin 6):ℂ) * PackedFace.wave n (packedSites 2 0 h 5) = _
      rw [packed_last]
      norm_num [charge,fiveSites] <;> ring
    · intro i _ hi
      simp [fiveSites,hi]
    · simp
  rw [structureFactor_packed,block_two] at hd
  have hhalf : PackedFace.wave n (1/2) = (((-1:ℝ)^n:ℝ):ℂ) := by
    simpa [PackedFace.wave] using exp_half_add n 0
  rw [exp_half_add,hhalf] at hd
  simp only [block, mul_one,Complex.ofReal_sub] at hd
  linear_combination hd

theorem structureFactor_fiveSites_sq (n : ℕ) (h t : ℝ) :
    ‖structureFactor (fiveSites h t) n‖^2 = fivePower (2*π*h) (2*π*t) n := by
  rw [structureFactor_fiveSites,Complex.sq_norm, Complex.normSq_sub]
  have hn := Complex.norm_exp_ofReal_mul_I (2*π*n*t)
  simp only [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, PackedFace.wave, hn, sq_abs,
    Complex.re_ofReal_mul, map_mul, Complex.conj_ofReal, Complex.conj_re,
    Complex.exp_ofReal_mul_I_re, fivePower]
  ring_nf

theorem structureFactor_triples_sq (n : ℕ) (h : ℝ) :
    ‖structureFactor (PackedFace.sites h 0) n‖^2 = triplePower (2*π*h) n := by
  rw [PackedFace.structureFactor_sites_sq, PackedFace.amplitude_eq_cos]
  simp [triplePower,triple]

end GaussianChains.Strip
