import ChainEnergy
import ChainGeometry
import PackedFaceGeometry
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Coordinates and first variations at the centered two-triple cell (Proposition 4).
The parameter t fixes the position of the first particle of the second triple.
A release increases one of the four gaps that equal the floor on the packed face. -/
namespace GaussianChains.Release

open scoped BigOperators Matrix

noncomputable section

def sites (h t : ℝ) (u : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![0, h + u 0, 2*h + u 0 + u 1, 1/2 + t,
    1/2 + t + h + u 2, 1/2 + t + 2*h + u 2 + u 3]

def gaps (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![x 1 - x 0, x 2 - x 1, x 3 - x 2, x 4 - x 3, x 5 - x 4, 1 + x 0 - x 5]

theorem zero_release_sites (h t : ℝ) : sites h t 0 = PackedFace.sites h t := by
  funext i
  fin_cases i <;> simp [sites, PackedFace.sites]

theorem gaps_eq_gap (x : Fin 6 → ℝ) (i : Fin 6) :
    gaps x i = GaussianChains.gap (by decide) x i := by
  fin_cases i <;> norm_num [gaps, GaussianChains.gap, liftSite, Fin.isValue]
  <;> ring_nf <;> rfl

def releaseCoordinates (h : ℝ) (x : Fin 6 → ℝ) : Fin 4 → ℝ :=
  ![x 1 - x 0 - h, x 2 - x 1 - h, x 4 - x 3 - h, x 5 - x 4 - h]

theorem reconstruct (x : Fin 6 → ℝ) (hx : x 0 = 0) (h : ℝ) :
    sites h (x 3 - 1/2) (releaseCoordinates h x) = x := by
  funext i
  fin_cases i <;> simp [sites, releaseCoordinates, hx] <;> ring

theorem releaseCoordinates_sites (h t : ℝ) (u : Fin 4 → ℝ) :
    releaseCoordinates h (sites h t u) = u := by
  funext i
  fin_cases i <;> simp [sites, releaseCoordinates] <;> ring

theorem feasible_iff (h t : ℝ) (u : Fin 4 → ℝ) :
    (∀ i, h ≤ gaps (sites h t u) i) ↔
    (∀ i, 0 ≤ u i) ∧
      3*h + u 0 + u 1 ≤ 1/2 + t ∧ 3*h + u 2 + u 3 ≤ 1/2 - t := by
  constructor
  · intro H
    have ht := H 2
    have hs := H 5
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa [gaps, sites] using H 0
      · change 0 ≤ u 1
        have := H 1; simp [gaps, sites] at this; linarith
      · change 0 ≤ u 2
        have := H 3; simp [gaps, sites] at this; linarith
      · change 0 ≤ u 3
        have := H 4; simp [gaps, sites] at this; linarith
    · simp [gaps, sites] at ht; linarith
    · simp [gaps, sites] at hs; linarith
  · rintro ⟨hu, ha, hb⟩ i
    fin_cases i <;> simp [gaps, sites] <;> linarith [hu 0, hu 1, hu 2, hu 3]

theorem model_feasible_iff (h t : ℝ) (u : Fin 4 → ℝ) :
    Feasible (by decide) h (sites h t u) ↔
      (∀ i, 0 ≤ u i) ∧
        3*h + u 0 + u 1 ≤ 1/2 + t ∧ 3*h + u 2 + u 3 ≤ 1/2 - t := by
  simpa only [Feasible, gaps_eq_gap] using feasible_iff h t u

/-- Ordered-pair energy for an arbitrary one-period kernel. -/
def pairEnergy (K : ℝ → ℝ) (x : Fin 6 → ℝ) : ℝ :=
  1 - (1/6) * ∑ i, ∑ j, ((-1 : ℝ)^i.val * (-1 : ℝ)^j.val) * K (x j - x i)

/-- First variation of the ordered-pair energy in a labelled velocity field. -/
def orderedVariation (D : ℝ → ℝ) (x v : Fin 6 → ℝ) : ℝ :=
  -((1/6) * ∑ i, ∑ j, ((-1 : ℝ)^i.val * (-1 : ℝ)^j.val) *
    (D (x j - x i) * (v j - v i)))

theorem pairEnergy_hasDerivAt (K D : ℝ → ℝ) (hK : ∀ z, HasDerivAt K (D z) z)
    (X : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (z : ℝ)
    (hX : ∀ i, HasDerivAt (fun w => X w i) (v i) z) :
    HasDerivAt (fun w => pairEnergy K (X w)) (orderedVariation D (X z) v) z := by
  unfold pairEnergy orderedVariation
  apply HasDerivAt.const_sub
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hK _).comp z ((hX j).sub (hX i))).const_mul _

/-- Slope of each inner gap in a centered cell. -/
def gapSlope (D : ℝ → ℝ) (h : ℝ) : ℝ :=
  (D h - D (2*h) + D (1/2-h) - D (1/2-2*h)) / 3

/-- D(xⱼ − xᵢ) at the centered cell. The four entries sampled from the odd
period-one force kernel occur at h, 2h, 1/2−h and 1/2−2h. -/
private def centerTable (a b c d : ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![0, a, b, 0, -c, -d], ![-a, 0, a, c, 0, -c], ![-b, -a, 0, d, c, 0],
    ![0, -c, -d, 0, a, b], ![c, 0, -c, -a, 0, a], ![d, c, 0, -b, -a, 0]]

set_option maxHeartbeats 800000 in
/-- Evaluate the force pattern after applying the centered half-turn and reflection. -/
private theorem table_variation (a b c d : ℝ) (v : Fin 6 → ℝ) :
    -((1/6 : ℝ) * ∑ i : Fin 6, ∑ j : Fin 6, ((-1 : ℝ)^i.val * (-1 : ℝ)^j.val) *
      (centerTable a b c d i j * (v j - v i))) =
    (a-b+c-d)/3 * (v 2 - v 0 + (v 5 - v 3)) := by
  let sign (i : Fin 6) : ℝ := (-1 : ℝ)^i.val
  let row (i : Fin 6) (a₀ a₁ a₂ a₃ a₄ a₅ : ℝ) : ℝ :=
    (sign i * sign 0) * (a₀ * (v 0 - v i)) + (sign i * sign 1) * (a₁ * (v 1 - v i)) +
    (sign i * sign 2) * (a₂ * (v 2 - v i)) + (sign i * sign 3) * (a₃ * (v 3 - v i)) +
    (sign i * sign 4) * (a₄ * (v 4 - v i)) + (sign i * sign 5) * (a₅ * (v 5 - v i))
  simp only [Fin.sum_univ_six]
  change -((1/6) * (row 0 0 a b 0 (-c) (-d) + row 1 (-a) 0 a c 0 (-c) +
    row 2 (-b) (-a) 0 d c 0 + row 3 0 (-c) (-d) 0 a b +
    row 4 c 0 (-c) (-a) 0 a + row 5 d c 0 (-b) (-a) 0)) = _
  norm_num [row, sign]
  ring

set_option maxHeartbeats 1000000 in
private theorem centered_variation (D : ℝ → ℝ) (hodd : ∀ z, D (-z) = -D z)
    (hper : Function.Periodic D 1) (h : ℝ) (v : Fin 6 → ℝ) :
    orderedVariation D (sites h 0 0) v =
      gapSlope D h * (v 2 - v 0 + (v 5 - v 3)) := by
  have hzero : D 0 = 0 := by
    have H := hodd 0
    rw [neg_zero] at H
    linarith
  have opp (x : ℝ) : D (1/2+x) = -D (1/2-x) := by
    calc
      D (1/2+x) = D (-(1/2-x)+1) := by congr 1; ring
      _ = D (-(1/2-x)) := hper _
      _ = -D (1/2-x) := hodd _
  have half : D (1/2) = 0 := by
    have H := opp 0
    simp only [add_zero, sub_zero] at H
    linarith
  have d1 := hodd h
  have d2 := hodd (2*h)
  have m0 := hodd (1/2 : ℝ)
  have m1 := hodd (1/2 - h)
  have m2 := hodd (1/2 - 2*h)
  have p1 := opp h
  have p2 := opp (2*h)
  have n1 := hodd (1/2 + h)
  have n2 := hodd (1/2 + 2*h)
  have vals (i j : Fin 6) : D (sites h 0 0 j - sites h 0 0 i) =
      centerTable (D h) (D (2*h)) (D (1/2-h)) (D (1/2-2*h)) i j := by
    ring_nf (config := { failIfUnchanged := false }) at d1 d2 m0 m1 m2 p1 p2 n1 n2 half
    fin_cases i <;> fin_cases j <;> simp [sites, centerTable] <;> ring_nf (config := { failIfUnchanged := false })
    all_goals linarith only [d1, d2, m0, m1, m2, n1, n2, p1, p2, hzero, half]
  unfold orderedVariation gapSlope
  simp_rw [vals]
  exact table_variation _ _ _ _ v

/-- The chart velocity in the original six site positions. -/
def chartVelocity (a b : ℝ) (w : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![0, a + w 0, 2*a + w 0 + w 1, b, b + a + w 2, b + 2*a + w 2 + w 3]

theorem centeredChart_hasDerivAt (K D : ℝ → ℝ) (hK : ∀ z, HasDerivAt K (D z) z)
    (hodd : ∀ z, D (-z) = -D z) (hper : Function.Periodic D 1)
    (h a b : ℝ) (w : Fin 4 → ℝ) :
    HasDerivAt (fun z => pairEnergy K (sites (h + a*z) (b*z) (fun i => w i*z)))
      (gapSlope D h * (4*a + ∑ i, w i)) 0 := by
  have hv (i : Fin 6) : HasDerivAt
      (fun z => sites (h+a*z) (b*z) (fun j => w j*z) i)
      (chartVelocity a b w i) 0 := by
    have line (z : ℝ) : sites (h+a*z) (b*z) (fun j => w j*z) i =
        (sites h 0 0 i) + chartVelocity a b w i * z := by
      fin_cases i <;> simp [sites, chartVelocity] <;> ring
    simp_rw [line]
    exact (hasDerivAt_const_mul (chartVelocity a b w i)).const_add _
  have H := pairEnergy_hasDerivAt K D hK _ _ 0 hv
  apply H.congr_deriv
  simp only [mul_zero, add_zero]
  change orderedVariation D (sites h 0 0) _ = _
  rw [centered_variation D hodd hper]
  apply congrArg (gapSlope D h * ·)
  simp [chartVelocity, Fin.sum_univ_four]
  ring

/-- The four one-sided release slopes are all one quarter of the derivative
along the packed branch. The derivatives here are computed on the ambient chart,
so in particular they restrict to inward rays in the nonnegative orthant. -/
theorem four_release_derivatives (K D : ℝ → ℝ) (hK : ∀ z, HasDerivAt K (D z) z)
    (hodd : ∀ z, D (-z) = -D z) (hper : Function.Periodic D 1) (h : ℝ) (j : Fin 4) :
    HasDerivAt (fun z => pairEnergy K (sites h 0 (fun i => if i = j then z else 0)))
      (deriv (fun v => pairEnergy K (sites v 0 0)) h / 4) 0 := by
  have floor := centeredChart_hasDerivAt K D hK hodd hper h 1 0 0
  simp at floor
  have dh : deriv (fun v => pairEnergy K (sites v 0 0)) h = gapSlope D h * 4 := by
    have key := deriv_comp_const_add (fun v => pairEnergy K (sites v 0 0)) h 0
    calc
      _ = deriv (fun z => pairEnergy K (sites (h+z) 0 0)) 0 := by simpa using key.symm
      _ = _ := floor.deriv
  have hj := centeredChart_hasDerivAt K D hK hodd hper h 0 0
    (fun i => if i = j then 1 else 0)
  rw [dh]
  simpa [ite_mul] using hj

private theorem kernel_eq_thetaKernel (s : ℝ) (hs : 0 < s) (z : ℝ) :
    kernel s z = HurwitzZeta.evenKernel z (s/Real.pi) :=
  (kernel_hasSum s z hs).tsum_eq

/-- Spatial analyticity of the image-sum kernel at fixed positive width, via the
theta functional equation and holomorphy of the theta function in its first variable. -/
theorem kernel_analyticAt (s : ℝ) (hs : 0 < s) (d : ℝ) :
    AnalyticAt ℝ (GaussianChains.kernel s) d := by
  let t := s/Real.pi
  let τ : ℂ := Complex.I * ((1/t : ℝ) : ℂ)
  have ht : 0 < t := div_pos hs Real.pi_pos
  have hτ : 0 < τ.im := by simpa [τ] using one_div_pos.mpr ht
  have expr (z : ℝ) : GaussianChains.kernel s z =
      (1 / t^(1/2 : ℝ)) * (jacobiTheta₂ (z : ℂ) τ).re := by
    rw [kernel_eq_thetaKernel s hs z, HurwitzZeta.evenKernel_functional_equation]
    congr 1
    exact congrArg Complex.re (HurwitzZeta.cosKernel_def z (1/t))
  have ha : Differentiable ℂ (fun z : ℂ => jacobiTheta₂ z τ) :=
    fun z => differentiableAt_jacobiTheta₂_fst z hτ
  have hb : AnalyticAt ℝ (fun z : ℂ => jacobiTheta₂ z τ) (d : ℂ) :=
    (ha.analyticAt _).restrictScalars
  simp_rw [funext expr]
  exact analyticAt_const.mul ((Complex.reCLM.analyticAt _).comp
    (hb.comp (Complex.ofRealCLM.analyticAt d)))

/-- Joint real analyticity in all labelled positions, including collisions. -/
theorem imageEnergy_analyticAt {N : ℕ} {s : ℝ} (hs : 0 < s) (x : Fin N → ℝ) :
    AnalyticAt ℝ (imageEnergy s) x := by
  have coord (i : Fin N) : AnalyticAt ℝ (fun v : Fin N → ℝ => v i) x :=
    (ContinuousLinearMap.proj (R := ℝ) i).analyticAt x
  unfold imageEnergy
  apply analyticAt_const.sub
  apply analyticAt_const.mul
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact analyticAt_const.mul ((kernel_analyticAt s hs _).comp ((coord j).sub (coord i)))

private theorem kernel_deriv_odd (s : ℝ) (hs : 0 < s) (z : ℝ) :
    deriv (kernel s) (-z) = -deriv (kernel s) z := by
  have he (u : ℝ) : kernel s (-u) = kernel s u := by
    rw [kernel_eq_thetaKernel s hs (-u), kernel_eq_thetaKernel s hs u,
      AddCircle.coe_neg, HurwitzZeta.evenKernel_neg]
  have h := deriv_comp_neg (kernel s) z
  simp_rw [he] at h
  linarith

private theorem kernel_deriv_periodic (s : ℝ) (hs : 0 < s) :
    Function.Periodic (deriv (kernel s)) 1 := by
  have hp (u : ℝ) : kernel s (u+1) = kernel s u := by
    rw [kernel_eq_thetaKernel s hs (u+1), kernel_eq_thetaKernel s hs u,
      AddCircle.coe_add_period]
  intro z
  have H := deriv_comp_add_const (kernel s) 1 z
  simpa only [hp] using H.symm

theorem pairEnergy_kernel (s : ℝ) (x : Fin 6 → ℝ) :
    pairEnergy (kernel s) x = imageEnergy s x := rfl

/-- Every inward partial derivative equals one fourth of the packed-floor
derivative for the actual six-site image energy, at every positive width. -/
theorem gaussian_four_release_derivatives (s : ℝ) (hs : 0 < s) (h : ℝ) (j : Fin 4) :
    HasDerivAt (fun z => imageEnergy s (sites h 0 (fun i => if i = j then z else 0)))
      (deriv (fun v => imageEnergy s (PackedFace.sites v 0)) h / 4) 0 := by
  simp_rw [← zero_release_sites]
  exact four_release_derivatives (kernel s) (deriv (kernel s))
    (fun z => (kernel_analyticAt s hs z).differentiableAt.hasDerivAt)
    (kernel_deriv_odd s hs) (kernel_deriv_periodic s hs) h j


/-- The release chart preserves real analyticity of parameter families. -/
theorem sites_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H T : E → ℝ} {U : E → Fin 4 → ℝ} {p : E} (hh : AnalyticAt ℝ H p)
    (ht : AnalyticAt ℝ T p) (hu : ∀ i, AnalyticAt ℝ (fun z => U z i) p) :
    AnalyticAt ℝ (fun z => sites (H z) (T z) (U z)) p := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact hh.add (hu 0)
  · exact ((analyticAt_const.mul hh).add (hu 0)).add (hu 1)
  · exact analyticAt_const.add ht
  · exact ((analyticAt_const.add ht).add hh).add (hu 2)
  · exact (((analyticAt_const.add ht).add (analyticAt_const.mul hh)).add (hu 2)).add (hu 3)

/-- Joint analyticity in the floor, displacement and four opened gaps. -/
theorem chartEnergy_analyticAt {s : ℝ} (hs : 0 < s) (p : ℝ × ℝ × (Fin 4 → ℝ)) :
    AnalyticAt ℝ (fun z : ℝ × ℝ × (Fin 4 → ℝ) => imageEnergy s (sites z.1 z.2.1 z.2.2)) p := by
  apply (imageEnergy_analyticAt hs _).comp
  let fst : (ℝ × ℝ × (Fin 4 → ℝ)) →L[ℝ] ℝ := ContinuousLinearMap.fst _ _ _
  let snd : (ℝ × ℝ × (Fin 4 → ℝ)) →L[ℝ] (ℝ × (Fin 4 → ℝ)) := ContinuousLinearMap.snd _ _ _
  let time : (ℝ × (Fin 4 → ℝ)) →L[ℝ] ℝ := ContinuousLinearMap.fst _ _ _
  let releases : (ℝ × (Fin 4 → ℝ)) →L[ℝ] (Fin 4 → ℝ) := ContinuousLinearMap.snd _ _ _
  apply sites_analyticAt (fst.analyticAt p) ((time.comp snd).analyticAt p)
  intro i
  let ev : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  exact ((ev.comp releases).comp snd).analyticAt p

/-- Fréchet derivative on each coordinate unit vector, for use in the
positive-inward-derivative test on the nonnegative release orthant. -/
theorem gaussian_release_partial {s : ℝ} (hs : 0 < s) (h : ℝ) (j : Fin 4) :
    fderiv ℝ (fun u => imageEnergy s (sites h 0 u)) 0 (Pi.single j 1) =
      deriv (fun v => imageEnergy s (PackedFace.sites v 0)) h / 4 := by
  let e : Fin 4 → ℝ := Pi.single j 1
  have smooth : AnalyticAt ℝ (fun u => imageEnergy s (sites h 0 u)) 0 :=
    (imageEnergy_analyticAt hs _).comp (sites_analyticAt analyticAt_const analyticAt_const
      (fun i => ((ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ)).analyticAt _))
  have ray : HasDerivAt (fun z : ℝ => z • e) e 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).smul_const e
  have hr := smooth.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 ray (by simp)
  have he (z : ℝ) : z • e = fun i => if i = j then z else 0 := by
    funext i
    by_cases hij : i = j
    · subst i; simp [e]
    · simp [e, hij]
  have goalRay := gaussian_four_release_derivatives s hs h j
  simp only [Function.comp_def, he] at hr
  exact hr.unique goalRay


end
end GaussianChains.Release

