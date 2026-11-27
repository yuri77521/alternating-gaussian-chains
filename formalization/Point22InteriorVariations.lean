import ChainMinimum
import ChainScore
import CertRootDerivative
import CertTreeVariations
import Point22Curvature
import Mathlib.Tactic.FunProp

/-! Single-label variations about a six-site ground state with six slack gaps.
The central self-field contribution is extracted explicitly from the Hessian. -/
noncomputable section
namespace GaussianChains.Point22.Interior
open GaussianChains.Root22 Filter Topology Set

private def velocity (i j : Fin 6) : ℝ := if j=i then 1 else 0
private def moved (i : Fin 6) (x : Fin 6 → ℝ) (t : ℝ) := fun j => x j + t * velocity i j

private def lineScore (F : ℝ → ℝ) (m : ℕ) (i : Fin 6) (x : Fin 6 → ℝ) (t : ℝ) :=
  ∑ j, ∑ k, charge j * charge k * (velocity i k-velocity i j)^m *
    F ((x k-x j) + t*(velocity i k-velocity i j))

private theorem lineScore_deriv {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x)
    (m : ℕ) (i : Fin 6) (x : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (lineScore F m i x) (lineScore D (m+1) i x t) t := by
  unfold lineScore
  apply HasDerivAt.fun_sum; intro j _
  apply HasDerivAt.fun_sum; intro k _
  let w := velocity i k-velocity i j
  have ha : HasDerivAt (fun u : ℝ => (x k-x j)+u*w) w t := by
    simpa only [Pi.add_apply,id_eq,zero_add,one_mul] using
      (hasDerivAt_const t (x k-x j)).add ((hasDerivAt_id t).mul_const w)
  have h := ((hF _).comp t ha).const_mul (charge j*charge k*w^m)
  convert h using 1
  simp only [pow_succ,w]
  ring

private theorem energy_line (i : Fin 6) (x : Fin 6 → ℝ) (t : ℝ) :
    imageEnergy 22 (moved i x t) = 1 - 1/6 * lineScore (kernel 22) 0 i x t := by
  have e (j k : Fin 6) : moved i x t k - moved i x t j =
      (x k-x j)+t*(velocity i k-velocity i j) := by unfold moved; ring
  simp [imageEnergy,e,lineScore]

theorem curvature_even (x : ℝ) : Curvature.kernel₂ (-x) = Curvature.kernel₂ x := by
  unfold Curvature.kernel₂
  conv_rhs => rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,Int.cast_neg,Curvature.gaussian₂]
  rw [show -x+(k:ℝ)= -(x+ -(k:ℝ)) by ring,neg_sq]

private theorem one_site_curvature (i : Fin 6) (x : Fin 6 → ℝ) :
    lineScore Curvature.kernel₂ 2 i x 0 = 2*(charge i *
      ∑ j, charge j*Curvature.kernel₂ (x i-x j) - Curvature.kernel₂ 0) := by
  let P (j : Fin 6) := charge i * (charge j * Curvature.kernel₂ (x i-x j))
  have ht (j k : Fin 6) :
      charge j*charge k*(velocity i k - velocity i j)^2 *
        Curvature.kernel₂ ((x k-x j)+0*(velocity i k-velocity i j)) =
      (if j=i then P k else 0) + (if k=i then P j else 0) -
        (if j=i then (if k=i then 2*Curvature.kernel₂ 0 else 0) else 0) := by
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k
      simp [P,velocity, ← mul_assoc,charge_mul_self]; ring
    · subst j
      simp [P,velocity,hk]
      rw [show x k-x i = -(x i-x k) by ring, curvature_even]
      ring
    · subst k
      simp [P,velocity,hj]; ring
    · simp [P,velocity,hj,hk]
  unfold lineScore
  simp_rw [ht,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp [P,Finset.mul_sum]
  ring

/-- Necessary second derivative sign at every site of a fully slack minimizer. -/
theorem slack_site_necessary {x : Fin 6 → ℝ} {h : ℝ}
    (hm : IsGroundState (by decide) h 22 x) (hs : ∀ j, h < gap (by decide) x j)
    (i : Fin 6) : charge i * (∑ j, charge j*Curvature.kernel₂ (x i-x j)) ≤ Curvature.kernel₂ 0 := by
  have hzero : moved i x 0 = x := by funext j; simp [moved]
  have hg (j : Fin 6) : Continuous (fun t => gap (by decide) (moved i x t) j) := by
    unfold gap liftSite moved
    fun_prop
  have hp : ∀ᶠ t : ℝ in 𝓝 0, Feasible (by decide) h (moved i x t) := by
    apply Filter.eventually_all.mpr
    intro j
    have h0 : 0 ∈ {t : ℝ | h < gap (by decide) (moved i x t) j} := by
      change h < gap (by decide) (moved i x 0) j
      rw [hzero]; exact hs j
    have he : ∀ᶠ t : ℝ in 𝓝 0, h < gap (by decide) (moved i x t) j :=
      (isOpen_lt continuous_const (hg j)).mem_nhds h0
    exact he.mono (fun y hy => hy.le)
  have hloc : IsLocalMax (lineScore (kernel 22) 0 i x) 0 := by
    filter_upwards [hp] with t ht
    have he : imageEnergy 22 (moved i x 0) ≤ imageEnergy 22 (moved i x t) :=
      (congrArg (imageEnergy 22) hzero).le.trans (hm.2 _ ht)
    rw [energy_line, energy_line] at he
    linarith
  have h₁ (t : ℝ) := lineScore_deriv hasDerivAt_kernel22 0 i x t
  have h₂ (t : ℝ) := lineScore_deriv hasDerivAt_derivKernel 1 i x t
  have hh := (Cert.necessary_transfer hloc (h₁ 0).continuousAt).2
  rw [show deriv (lineScore (kernel 22) 0 i x) = lineScore derivKernel 1 i x from
    funext (fun t => (h₁ t).deriv), (h₂ 0).deriv] at hh
  change lineScore Curvature.kernel₂ 2 i x 0 ≤ 0 at hh
  rw [one_site_curvature] at hh
  linarith

end GaussianChains.Point22.Interior
