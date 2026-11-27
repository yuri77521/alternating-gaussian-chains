import PackedFaceCalculus
import PackedFaceModesEnergy
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The endpoint slopes are genuine one-sided derivatives. The derivative in the
unconstrained signed displacement has the centered curvature used in Proposition 4. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set Filter
open scoped Topology

private theorem deriv_on_closed {F D : ℝ → ℝ} (hf : ContinuousOn F (Icc 0 2))
    (hD : ContinuousOn D (Icc 0 2)) (hd : ∀ y ∈ Ioo 0 2, HasDerivAt F (D y) y)
    {y : ℝ} (hy : y ∈ Icc 0 2) : HasDerivWithinAt F (D y) (Icc 0 2) y := by
  have hab : (0:ℝ) < 2 := by norm_num
  have hdiff : DifferentiableOn ℝ F (Ioo 0 2) := fun z hz =>
    (hd z hz).differentiableAt.differentiableWithinAt
  rcases eq_or_lt_of_le hy.1 with rfl | hl
  · apply HasDerivWithinAt.mono _ Icc_subset_Ici_self
    apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff ((hf 0 hy).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
    apply ((hD 0 hy).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hab)).tendsto.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with z hz
    exact (hd z hz).deriv.symm
  rcases eq_or_lt_of_le hy.2 with rfl | hr
  · apply HasDerivWithinAt.mono _ Icc_subset_Iic_self
    apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff ((hf 2 hy).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
    apply ((hD 2 hy).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hab)).tendsto.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with z hz
    exact (hd z hz).deriv.symm
  exact (hd _ ⟨hl,hr⟩).hasDerivWithinAt

theorem hasDerivWithinAt_phi {q h y : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) (hy : y ∈ Icc 0 2) :
    HasDerivWithinAt (phi q h) (phiD q h y) (Icc 0 2) y :=
  deriv_on_closed (continuousOn_phi hq hQ) (continuousOn_phiD hq hQ) (fun _ => hasDerivAt_phi hq hQ) hy

theorem hasDerivWithinAt_phiD {q h y : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) (hy : y ∈ Icc 0 2) :
    HasDerivWithinAt (phiD q h) (phiDD q h y) (Icc 0 2) y :=
  deriv_on_closed (continuousOn_phiD hq hQ) (continuousOn_phiDD hq hQ) (fun _ => hasDerivAt_phiD hq hQ) hy

private theorem coord_range (v : ℝ) : coord v ∈ Icc 0 2 := by
  unfold coord
  constructor <;> linarith [Real.cos_le_one (2*Real.pi*v),Real.neg_one_le_cos (2*Real.pi*v)]

private theorem hasDerivAt_coord (v : ℝ) :
    HasDerivAt coord (2*Real.pi * Real.sin (2*Real.pi*v)) v := by
  have ht := (hasDerivAt_id v).const_mul (2*Real.pi)
  convert (ht.cos.const_sub 1) using 1 <;> simp [coord,mul_comm]

/-- First derivative throughout the signed-displacement line, including both
endpoint values of its squared-displacement coordinate. -/
theorem deriv_energy_displacement {s : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ faceQ) (h t : ℝ) :
    deriv (fun v => imageEnergy s (sites h v)) t =
      (4 * Real.sqrt (Real.pi/s) * Real.exp (-(Real.pi^2)/s)/6) *
      (phiD (Real.exp (-(Real.pi^2)/s)) h (coord t) *
        ((2*Real.pi) * Real.sin ((2*Real.pi)*t))) := by
  let q := Real.exp (-(Real.pi^2)/s)
  let C := 4*Real.sqrt (Real.pi/s)*q/6
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hE : (fun u => imageEnergy s (sites h u)) =
      (fun u => C * phi q h (coord u) + imageEnergy s (sites h 0)) := by
    funext u
    exact sub_eq_iff_eq_add.mp (imageEnergy_difference hs h u)
  rw [hE]
  have hd := (hasDerivWithinAt_phi (h := h) hq hQ (coord_range t)).comp_hasDerivAt t
    (hasDerivAt_coord t) (Eventually.of_forall coord_range)
  exact ((hd.const_mul C).add_const _).deriv

/-- The curvature in the signed displacement is a positive multiple of the true closed-interval
slope in the squared coordinate, also when that slope vanishes. -/
theorem centered_curvature {s : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ faceQ) (h : ℝ) :
    deriv (deriv (fun t => imageEnergy s (sites h t))) 0 =
      (4 * Real.sqrt (Real.pi/s) * Real.exp (-(Real.pi^2)/s)/6) *
      (2*Real.pi)^2 * phiD (Real.exp (-(Real.pi^2)/s)) h 0 := by
  let q := Real.exp (-(Real.pi^2)/s)
  let C := 4*Real.sqrt (Real.pi/s)*q/6
  let w := 2*Real.pi
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hfirst : deriv (fun u => imageEnergy s (sites h u)) =
      (fun u => C * (phiD q h (coord u) * (w * Real.sin (w*u)))) :=
    funext (deriv_energy_displacement hs hQ h)
  have hd := (hasDerivWithinAt_phiD (h := h) hq hQ (coord_range 0)).comp_hasDerivAt 0
    (hasDerivAt_coord 0) (Eventually.of_forall coord_range)
  have hsin := (((hasDerivAt_id (0:ℝ)).const_mul w).sin).const_mul w
  have hcalc := ((hd.mul hsin).const_mul C).deriv
  rw [hfirst]
  convert hcalc using 1 <;> simp [w,C,q,Function.comp_def] <;> ring

end GaussianChains.PackedFace


