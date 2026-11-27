import ClustersSelection
import ClustersWidthKernel

/-! Scalar Taylor bounds at the two antipodes and equation (5) for the actual
angular Gaussian Fourier kernel. `η` is an angular gap. -/

noncomputable section
open Finset Real
namespace GaussianChains.Clusters

/-- At zero and π all odd sine sums vanish. Four integrations of the
absolute fourth-derivative majorant supply the constants in the contact and
midpoint estimates (the first step bounds the third derivative). -/
theorem angular_taylor_bounds {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3)
    {c : ℝ} (hc : c = 0 ∨ c = π) (z : ℝ) :
    |-angularCos 2 q (c+z)+angularCos 2 q c| ≤ |z|^2 ∧
    |-angularSin 1 q (c+z)+angularCos 2 q c*z| ≤ |z|^3/3 ∧
    |angularK q (c+z)-angularK q c+angularCos 2 q c*z^2/2| ≤ |z|^4/12 := by
  have hsin (n : ℕ) : angularSin n q c = 0 := by rcases hc with rfl | rfl <;> simp
  have dcos (p : ℕ) (t : ℝ) : HasDerivAt (fun u => angularCos p q (c+u))
      (-angularSin (p+1) q (c+t)) t := by
    simpa [Function.comp_def] using (angularCos_hasDerivAt hq hq' p (c+t)).comp t
      ((hasDerivAt_id t).const_add c)
  have dsin (p : ℕ) (t : ℝ) : HasDerivAt (fun u => angularSin p q (c+u))
      (angularCos (p+1) q (c+t)) t := by
    simpa [Function.comp_def] using (angularSin_hasDerivAt hq hq' p (c+t)).comp t
      ((hasDerivAt_id t).const_add c)
  have h3 (t : ℝ) : |angularSin 3 q (c+t)| ≤ 2*|t| := by
    simpa using primitive_abs_bound _ _ 2 0 (dsin 3)
      (fun t => by simpa using (locking_curvature_bounds hq hq' hR (c+t)).2.1.le)
      (by simp [hsin]) t
  have h2 (t : ℝ) : |-angularCos 2 q (c+t)+angularCos 2 q c| ≤ |t|^2 := by
    have hh := primitive_abs_bound _ _ 2 1
      (fun t => ((dcos 2 t).neg.add_const (angularCos 2 q c)))
      (fun t => by simpa using h3 t) (by simp) t
    norm_num at hh
    simpa only [sq_abs] using hh
  have h1 (t : ℝ) : |-angularSin 1 q (c+t)+angularCos 2 q c*t| ≤ |t|^3/3 := by
    have hh := primitive_abs_bound _ _ 1 2
      (fun t => (dsin 1 t).neg.add ((hasDerivAt_id t).const_mul (angularCos 2 q c)))
      (fun t => by simpa using h2 t) (by simp [hsin]) t
    norm_num at hh
    linarith only [hh]
  refine ⟨h2 z, h1 z, ?_⟩
  have dF (t : ℝ) : HasDerivAt
      (fun u => angularK q (c+u)-angularK q c+angularCos 2 q c*u^2/2)
      (-angularSin 1 q (c+t)+angularCos 2 q c*t) t := by
    convert ((dcos 0 t).sub_const (angularK q c)).add
      ((((hasDerivAt_id t).pow 2).const_mul (angularCos 2 q c)).div_const 2) using 1 <;> simp <;> ring
  have hh := primitive_abs_bound _ _ (1/3) 3 dF
    (fun t => by linarith only [h1 t]) (by simp) z
  norm_num at hh
  linarith only [hh]

/-- The uniform fourth-order remainder in (5) for the actual kernel and any
two localized odd blocks. Both directions of the cross sum are included. -/
theorem gaussian_two_block_taylor {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x : α → ℝ) (y : β → ℝ)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hw' : ∀ i, |w i|=1) (hv' : ∀ j, |v j|=1)
    {q C η : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3)
    (hx : ∀ i, |x i| ≤ C*η) (hy : ∀ j, |y j| ≤ C*η) :
    let P₀ := ∑ i, w i*x i
    let Pπ := ∑ i, v i*y i
    let V₀ := (∑ i, w i*(x i)^2)-P₀^2
    let Vπ := (∑ i, v i*(y i)^2)-Pπ^2
    let N := (Fintype.card α : ℝ)+(Fintype.card β : ℝ)
    let D := angularCos 2 q 0-angularCos 2 q π
    let K := angularK q
    let F := 2*(K 0-K π)-blockSum w w x x K 0-blockSum v v y y K 0+
      2*blockSum w v x y K π
    |F - (D*(V₀+Vπ) - angularCos 2 q π*(P₀-Pπ)^2)| ≤ 4/3*N^2*C^4*η^4 := by
  have pair {c u t : ℝ} (hc : c=0 ∨ c=π) (hu : |u|≤C*η) (ht : |t|≤C*η) :
      |angularK q (c+(u-t))-angularK q c-(-angularCos 2 q c)/2*(u-t)^2| ≤
        4/3*C^4*η^4 := by
    have hsum : |u-t| ≤ |u|+|t| := by simpa using abs_sub_le u 0 t
    have hdiff : |u-t| ≤ 2*(C*η) := by linarith
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hdiff 4
    calc
      _ = |angularK q (c+(u-t))-angularK q c+angularCos 2 q c*(u-t)^2/2| :=
        congrArg abs (by ring)
      _ ≤ |u-t|^4/12 := (angular_taylor_bounds hq hq' hR hc (u-t)).2.2
      _ ≤ (2*(C*η))^4/12 := div_le_div_of_nonneg_right hpow (by norm_num)
      _ = _ := by ring
  have h := two_block_taylor w v x y (angularK q) (-angularCos 2 q 0) (-angularCos 2 q π)
    (4/3*C^4*η^4) hw hv hw' hv' (fun i j => pair (Or.inl rfl) (hx i) (hx j))
    (fun i j => pair (Or.inl rfl) (hy i) (hy j))
    (fun i j => pair (Or.inr rfl) (hx i) (hy j))
  dsimp only at h ⊢
  convert h using 1
  · apply congrArg abs
    ring
  · ring

#print axioms angular_taylor_bounds
#print axioms gaussian_two_block_taylor


/-- A path of relative coordinates through the ordered pairs, one affine
velocity per pair. Center angles are either zero or π. -/
def pairPath {ι : Type*} [Fintype ι] (q : ℝ) (w c x velocity : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i*angularK q (c i + (x i + t*velocity i))

/-- The derivative along the actual kernel path differs from the derivative
of its pairwise quadratic Taylor polynomial by the cubic error per pair.
For an ordered `Fin N × Fin N` index the prefactor is exactly `N²`. -/
theorem pairPath_derivative {ι : Type*} [Fintype ι] (w c x velocity : ι → ℝ)
    {q C η : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3)
    (hw : ∀ i, |w i|=1) (hc : ∀ i, c i=0 ∨ c i=π)
    (hx : ∀ i, |x i| ≤ 2*C*η) (hv : ∀ i, |velocity i| ≤ 1) :
    ∃ dF, HasDerivAt (pairPath q w c x velocity) dF 0 ∧
      |dF - ∑ i, w i*((-angularCos 2 q (c i)*x i)*velocity i)| ≤
        (Fintype.card ι : ℝ)*(8/3*C^3*η^3) := by
  classical
  let A (i : ι) := -angularSin 1 q (c i+x i)
  let B (i : ι) := -angularCos 2 q (c i)*x i
  refine ⟨∑ i, w i*(A i*velocity i), ?_, ?_⟩
  · apply HasDerivAt.fun_sum
    intro i _
    have arg : HasDerivAt (fun t : ℝ => c i+(x i+t*velocity i)) (velocity i) 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).mul_const (velocity i)).const_add (x i)).const_add (c i)
    have h := (angularCos_hasDerivAt hq hq' 0 (c i+(x i+0*velocity i))).comp 0 arg
    simpa [A, Function.comp_def, angularK] using h.const_mul (w i)
  · change |(∑ i, w i*(A i*velocity i)) - ∑ i, w i*(B i*velocity i)| ≤ _
    rw [← sum_sub_distrib]
    have hb (i : ι) : |A i-B i| ≤ (8/3)*C^3*η^3 := by
      have h := (angular_taylor_bounds hq hq' hR (hc i) (x i)).2.1
      have h' := pow_le_pow_left₀ (abs_nonneg _) (hx i) 3
      dsimp [A,B]
      rw [neg_mul,sub_neg_eq_add]
      nlinarith only [h,h']
    have term (i : ι) : |w i*(A i*velocity i)-w i*(B i*velocity i)| ≤ 8/3*C^3*η^3 := by
      rw [show w i*(A i*velocity i)-w i*(B i*velocity i) = w i*(A i-B i)*velocity i by ring,
        abs_mul,abs_mul,hw,one_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hv i)).trans (hb i)
    calc
      _ ≤ ∑ i, |w i*(A i*velocity i)-w i*(B i*velocity i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, 8/3*C^3*η^3 := sum_le_sum fun i _ => term i
      _ = _ := by simp

/-- A strictly positive derivative supplies a lower-energy feasible move
arbitrarily close to zero on the *decreasing* side, which suffices even on
the boundary of the outer-gap constraint. -/
theorem eventually_lower_left {f : ℝ → ℝ} {dF : ℝ}
    (hf : HasDerivAt f dF 0) (h : 0 < dF) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0), f t < f 0 := by
  have hs := ((hasDerivAt_iff_tendsto_slope_left_right.mp hf).1).eventually
    (lt_mem_nhds h)
  filter_upwards [hs, self_mem_nhdsWithin] with t hpos ht
  exact (slope_pos_iff_of_le (show t ≤ 0 from le_of_lt ht)).mp ((slope_comm f 0 t) ▸ hpos)

#print axioms pairPath_derivative

end GaussianChains.Clusters

