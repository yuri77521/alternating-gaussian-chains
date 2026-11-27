import ClustersContactPath
import ClustersSelectionKernel

noncomputable section
namespace GaussianChains.Clusters

open Real Finset OddBlock

/-- Kernel minus the variable quadratic Taylor term, summed over a block pair.
Its constant term has no effect on the gap derivative. -/
def pathResidual {α β : Type*} [Fintype α] [Fintype β]
    (q c : ℝ) (w : α → ℝ) (v : β → ℝ) (x vx : α → ℝ) (y vy : β → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, w i*v j *
    (let z := (x i-y j) + t*(vx i-vy j)
     angularK q (c+z) + angularCos 2 q c / 2 * z^2)

/-- The Taylor error differentiated along an actual site path. The pair count
is kept explicit so that the two self blocks and both cross blocks can be
combined with the coefficient of the published small-floor condition. -/
theorem pathResidual_derivative {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x vx : α → ℝ) (y vy : β → ℝ)
    {q c C η : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3)
    (hc : c=0 ∨ c=π) (hw : ∀ i, |w i|=1) (hv : ∀ j, |v j|=1)
    (hx : ∀ i, |x i| ≤ C*η) (hy : ∀ j, |y j| ≤ C*η)
    (hspeed : ∀ i j, |vx i-vy j| ≤ 1) :
    ∃ dR, HasDerivAt (pathResidual q c w v x vx y vy) dR 0 ∧
      |dR| ≤ (Fintype.card α : ℝ)*(Fintype.card β : ℝ)*(8/3*C^3*η^3) := by
  let D (i : α) (j : β) := w i*v j *
    ((-angularSin 1 q (c+(x i-y j)) + angularCos 2 q c*(x i-y j))*(vx i-vy j))
  refine ⟨∑ i, ∑ j, D i j, ?_, ?_⟩
  · let X (i : α) (j : β) (t : ℝ) := (x i-y j) + t*(vx i-vy j)
    have hX (i : α) (j : β) : HasDerivAt (X i j) (vx i-vy j) 0 := by
      simpa [X] using ((hasDerivAt_id (0:ℝ)).mul_const (vx i-vy j)).const_add (x i-y j)
    unfold pathResidual
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    have hK := (angularCos_hasDerivAt hq hq' 0 (c+X i j 0)).comp 0 ((hX i j).const_add c)
    have hQ := ((hX i j).pow 2).const_mul (angularCos 2 q c / 2)
    convert (hK.add hQ).const_mul (w i*v j) using 1
    simp only [D,X,zero_mul,add_zero,Nat.reduceAdd,Nat.reduceSub,pow_one,Nat.cast_ofNat]
    ring
  · have hε (i : α) (j : β) : |D i j| ≤ 8/3*C^3*η^3 := by
      have he := (angular_taylor_bounds hq hq' hR hc (x i-y j)).2.1
      have hl := (abs_sub_le (x i) 0 (y j))
      simp only [sub_zero, zero_sub, abs_neg] at hl
      have hd : |x i - y j| ≤ 2*C*η := by linarith [hx i,hy j]
      have hb := pow_le_pow_left₀ (abs_nonneg _) hd 3
      simp only [D, abs_mul, hw, hv, one_mul] 
      exact (mul_le_of_le_one_right (abs_nonneg _) (hspeed i j)).trans
        (by linarith only [he, hb])
    calc
      _ ≤ ∑ i, |∑ j, D i j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |D i j| := sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : α, ∑ _j : β, 8/3*C^3*η^3 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hε i j
      _ = _ := by simp; ring

/-- Recombine the error and its quadratic piece. -/
theorem pathResidual_eq {α β : Type*} [Fintype α] [Fintype β]
    (q c : ℝ) (w : α → ℝ) (v : β → ℝ) (x vx : α → ℝ) (y vy : β → ℝ) (t : ℝ) :
    let X := fun i => x i+t*vx i
    let Y := fun j => y j+t*vy j
    pathResidual q c w v x vx y vy t = blockSum w v X Y (angularK q) c +
      angularCos 2 q c/2 * (∑ i, ∑ j, w i*v j*(X i-Y j)^2) := by
  dsimp only
  unfold pathResidual blockSum
  rw [mul_sum, ←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [mul_sum, ←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [show x i-y j+t*(vx i-vy j)=x i+t*vx i-(y j+t*vy j) by ring]
  ring

/-- Along a motion of the first block at fixed first moment, the quadratic
part differentiates to `D*dV`. The remainder counts exactly the moving
ordered pairs, then uses the looser `N²` constant of the paper. -/
theorem contact_derivative_pos {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x vx : α → ℝ) (y : β → ℝ)
    {q C η dV : ℝ}
    (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hw' : ∀ i, |w i|=1) (hv' : ∀ j, |v j|=1)
    (hC : 1 ≤ C) (hη : 0 < η)
    (hN : 0 < (Fintype.card α : ℝ)+(Fintype.card β : ℝ))
    (hsmall : η ≤ 1 / (((Fintype.card α : ℝ)+(Fintype.card β : ℝ))*C^2))
    (hx : ∀ i, |x i| ≤ C*η) (hy : ∀ j, |y j| ≤ C*η)
    (hs₁ : ∀ i, |vx i| ≤ 1) (hs₂ : ∀ i j, |vx i-vx j| ≤ 1)
    (hP : ∀ t : ℝ, ∑ i, w i*(x i+t*vx i) = ∑ i, w i*x i)
    (hV : HasDerivAt (fun t : ℝ => (∑ i, w i*(x i+t*vx i)^2) -
      (∑ i, w i*(x i+t*vx i))^2) dV 0) (hdV : 2*η ≤ dV) :
    let X := fun (t : ℝ) i => x i+t*vx i
    let K := angularK q
    ∃ dF > 0, HasDerivAt (fun t => 2*(K 0-K π) -
      blockSum w w (X t) (X t) K 0 - blockSum v v y y K 0 +
      2*blockSum w v (X t) y K π) dF 0 := by
  let z : β → ℝ := fun _ => 0
  let Rxx := pathResidual q 0 w w x vx x vx
  let Rxy := pathResidual q π w v x vx y z
  let a := angularCos 2 q 0
  let b := angularCos 2 q π
  let D := a-b
  let V (t : ℝ) := (∑ i, w i*(x i+t*vx i)^2) - (∑ i, w i*(x i+t*vx i))^2
  let C₀ := 2*(angularK q 0-angularK q π)-blockSum v v y y (angularK q) 0 -
    b*((∑ j, v j*(y j)^2)-(∑ j, v j*y j)^2 + ((∑ i, w i*x i)-∑ j, v j*y j)^2)
  have eqn (t : ℝ) :
      (D*V t + (2*Rxy t - Rxx t) + C₀) =
      2*(angularK q 0-angularK q π) -
      blockSum w w (fun i => x i+t*vx i) (fun i => x i+t*vx i) (angularK q) 0 -
      blockSum v v y y (angularK q) 0 +
      2*blockSum w v (fun i => x i+t*vx i) y (angularK q) π := by
    dsimp only [D,a,b,V,C₀,Rxx,Rxy]
    rw [pathResidual_eq,pathResidual_eq]
    simp only [z, mul_zero, add_zero]
    rw [within_quadratic w _ hw, cross_quadratic w v _ _ hw hv, hP]
    ring
  obtain ⟨d₁,hr₁,hb₁⟩ := pathResidual_derivative w w x vx x vx hq hq' hR
    (Or.inl rfl) hw' hw' hx hx hs₂
  obtain ⟨d₂,hr₂,hb₂⟩ := pathResidual_derivative w v x vx y z hq hq' hR
    (Or.inr rfl) hw' hv' hx hy (fun i j => by simpa [z] using hs₁ i)
  have hD : 2 ≤ D := (locking_D_bounds hq hq' hR).1
  have he : 0 ≤ 8/3*C^3*η^3 := by positivity
  have hmargin := gap_derivative_margin hN hC hη hsmall hD
  have hlead := mul_le_mul_of_nonneg_left hdV (show 0 ≤ D by linarith)
  have herr : 2*d₂-d₁ ≥ -(((Fintype.card α : ℝ)+(Fintype.card β : ℝ))^2*(8/3*C^3*η^3)) := by
    have h₁ := (abs_le.mp hb₁).2
    have h₂ := (abs_le.mp hb₂).1
    nlinarith only [h₁,h₂,mul_nonneg (sq_nonneg (Fintype.card β : ℝ)) he]
  refine ⟨D*dV+(2*d₂-d₁), by nlinarith only [herr,hlead,hmargin], ?_⟩
  have hd := (((hV.const_mul D).add ((hr₂.const_mul 2).sub hr₁)).add_const C₀)
  convert hd using 1
  funext t
  exact (eqn t).symm

end GaussianChains.Clusters
