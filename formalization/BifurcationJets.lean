import BifurcationJetDefs
import ChainEnergy
import PackedFaceGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The interval expressions are derivatives of the actual six-particle energy. -/
noncomputable section
namespace GaussianChains.Bifurcation.Images
open Set GaussianChains.PackedFace
open scoped Topology

theorem kernelD_value (x : ℝ) : kernelD .value x = kernel 8 x := by
  simp [kernelD,term,polynomial,kernel]

private def parity : Order → ℝ
  | .first | .third => -1
  | _ => 1

private theorem kernelD_reflection (o : Order) (x : ℝ) :
    kernelD o (1-x) = parity o * kernelD o x := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun k => -k-1, invFun := fun k => -k-1,
      left_inv := fun k => by dsimp; ring, right_inv := fun k => by dsimp; ring }
  have HH (k : ℤ) : term o (1-x) k = parity o * term o x (e k) := by
    unfold term
    dsimp [e]
    push_cast
    rw [show x + (-(k:ℝ)-1) = -(1-x+k) by ring,neg_sq]
    cases o <;> dsimp [polynomial,parity] <;> ring
  simp only [kernelD, HH, tsum_mul_left, e.tsum_eq]

private theorem kernel_even₈ (x : ℝ) : kernel 8 (-x) = kernel 8 x := by
  have hh (k : ℤ) : Real.exp (-8*(-x+(k:ℝ))^2) =
      Real.exp (-8*(x+((-k:ℤ):ℝ))^2) := by push_cast; congr 1; ring
  unfold kernel
  simp only [hh]
  exact (Equiv.neg ℤ).tsum_eq (fun k : ℤ => Real.exp (-8*(x+(k:ℝ))^2))

def cross (o : Order) (h t : ℝ) :=
  (3*kernelD o (1/2+t)-2*kernelD o (1/2+t+h)-2*kernelD o (1/2+t-h)
    +kernelD o (1/2+t+2*h)+kernelD o (1/2+t-2*h))/3

private theorem algebra (K : ℝ → ℝ) (hK : ∀ x, K (-x) = K x) (h v : ℝ) :
    let X : Fin 6 → ℝ := ![0,h,2*h,v,v+h,v+2*h]
    1-(1/6:ℝ)*∑ i, ∑ j, charge i*charge j*K (X j-X i) =
      1-K 0 + (4*K h-2*K (2*h))/3 +
      (3*K v-2*K (v+h)-2*K (v-h)+K (v+2*h)+K (v-2*h))/3 := by
  have H₁ := hK h
  have H₂ := hK (2*h)
  have H₃ := hK v
  have H₄ := hK (v+h)
  have H₅ := hK (v-h)
  have H₆ := hK (v+2*h)
  have H₇ := hK (v-2*h)
  let X : Fin 6 → ℝ := ![0,h,2*h,v,v+h,v+2*h]
  change 1-(1/6:ℝ)*∑ i, ∑ j, charge i*charge j*K (X j-X i) = _
  have x0 : X 0 = 0 := rfl
  have c0 : charge (0:Fin 6) = 1 := by norm_num [charge]
  have x1 : X 1 = h := rfl
  have c1 : charge (1:Fin 6) = -1 := by norm_num [charge]
  have x2 : X 2 = 2*h := rfl
  have c2 : charge (2:Fin 6) = 1 := by norm_num [charge]
  have x3 : X 3 = v := rfl
  have c3 : charge (3:Fin 6) = -1 := by norm_num [charge]
  have x4 : X 4 = v+h := rfl
  have c4 : charge (4:Fin 6) = 1 := by norm_num [charge]
  have x5 : X 5 = v+2*h := rfl
  have c5 : charge (5:Fin 6) = -1 := by norm_num [charge]
  simp only [Fin.sum_univ_six,x0,x1,x2,x3,x4,x5,c0,c1,c2,c3,c4,c5]
  ring_nf at H₁ H₂ H₃ H₄ H₅ H₆ H₇ ⊢
  simp only [H₁,H₂,H₃,H₄,H₅,H₆,H₇]
  ring

theorem energy_cross (h t : ℝ) :
    imageEnergy 8 (sites h t) =
      1-kernel 8 0 + (4*kernel 8 h-2*kernel 8 (2*h))/3 + cross .value h t := by
  simpa only [imageEnergy,sites,cross,kernelD_value,Nat.cast_ofNat] using
    algebra (kernel 8) kernel_even₈ h (1/2+t)

private abbrev window := Ioo (-1/12:ℝ) (1/12)
private abbrev floors := Ioo (0:ℝ) (1/6)

private theorem cross_hasDerivAt {h t : ℝ} (hh : h ∈ floors) (ht : t ∈ window)
    (o : Order) (ho : o ≠ .fourth) :
    HasDerivAt (cross o h) (cross (next o) h t) t := by
  have H (a : ℝ) (ha : -(1/3) ≤ a ∧ a ≤ 1/3) :
      HasDerivAt (fun t : ℝ => kernelD o (1/2+t+a)) (kernelD (next o) (1/2+t+a)) t := by
    have hv : 1/2+t+a ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [ht.1,ha.1],by linarith [ht.2,ha.2]⟩
    simpa using (kernelD_hasDerivAt o ho hv).comp t (((hasDerivAt_id' t).const_add (1/2)).add_const a)
  have H₀ := H 0 (by constructor <;> norm_num)
  have Hp := H h ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have Hm := H (-h) ⟨by linarith [hh.2],by linarith [hh.1]⟩
  have Hp₂ := H (2*h) ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have Hm₂ := H (-(2*h)) ⟨by linarith [hh.2],by linarith [hh.1]⟩
  simpa only [cross,add_zero,sub_eq_add_neg] using
    (((((H₀.const_mul 3).sub (Hp.const_mul 2)).sub (Hm.const_mul 2)).add Hp₂).add Hm₂).div_const 3

private theorem curv_center (o : Order) (h : ℝ) (hp : parity o = 1) :
    cross o h 0 = curvatureAt o h := by
  have he (v : ℝ) : kernelD o (1/2-v) = kernelD o (1/2+v) := by
    rw [show 1/2-v=1-(1/2+v) by ring, kernelD_reflection, hp, one_mul]
  unfold cross curvatureAt
  simp only [add_zero,he]
  ring

theorem physical_centered_jets {h : ℝ} (hh : h ∈ floors) :
    deriv (deriv (fun t => imageEnergy 8 (sites h t))) 0 = curvatureAt .second h ∧
    iteratedDeriv 4 (fun t => imageEnergy 8 (sites h t)) 0 = curvatureAt .fourth h := by
  let f (t : ℝ) := imageEnergy 8 (sites h t)
  have h₁ : EqOn (deriv f) (cross .first h) window := by
    intro t ht
    have hf : f = fun v => (1-kernel 8 0 + (4*kernel 8 h-2*kernel 8 (2*h))/3) + cross .value h v :=
      funext (energy_cross h)
    rw [hf]
    exact ((cross_hasDerivAt hh ht .value (by decide)).const_add _).deriv
  have step {g : ℝ → ℝ} {o : Order} (hEq : EqOn g (cross o h) window) (ho : o ≠ .fourth) :
      EqOn (deriv g) (cross (next o) h) window := by
    intro t ht
    exact (hEq.deriv isOpen_Ioo ht).trans (cross_hasDerivAt hh ht o ho).deriv
  have h₂ := step h₁ (by decide)
  have h₃ := step h₂ (by decide)
  have h₄ := step h₃ (by decide)
  have hz : (0:ℝ) ∈ window := ⟨by norm_num,by norm_num⟩
  refine ⟨(h₂ hz).trans (curv_center .second h rfl),?_⟩
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (h₄ hz).trans (curv_center .fourth h rfl)

theorem mixedAt_physical {h : ℝ} (hh : h ∈ floors) :
    deriv (fun v => deriv (deriv (fun t => imageEnergy 8 (sites v t))) 0) h = mixedAt h := by
  have he : EqOn (fun v => deriv (deriv (fun t => imageEnergy 8 (sites v t))) 0)
      (curvatureAt .second) floors := fun _ hv => (physical_centered_jets hv).1
  rw [he.deriv isOpen_Ioo hh]
  have H (n : ℝ) (hn : n = 1 ∨ n = 2) :
      HasDerivAt (fun v => kernelD .second (1/2+n*v)) (kernelD .third (1/2+n*h)*n) h := by
    have hArg : 1/2+n*h ∈ Ioo (-1:ℝ) 1 := by
      rcases hn with rfl|rfl <;> constructor <;> linarith [hh.1,hh.2]
    simpa using (kernelD_hasDerivAt .second (by decide) hArg).comp h
      (((hasDerivAt_id' h).const_mul n).const_add (1/2))
  have h₁ := H 1 (Or.inl rfl)
  have h₂ := H 2 (Or.inr rfl)
  simp only [one_mul,mul_one] at h₁
  unfold mixedAt
  convert (((hasDerivAt_const h (3*kernelD .second (1/2))).sub (h₁.const_mul 4)).add
    (h₂.const_mul 2)).div_const 3 |>.deriv using 1 <;> try ring

theorem inwardAt_physical {h : ℝ} (hh : h ∈ floors) :
    deriv (fun v => imageEnergy 8 (sites v 0)) h / 4 = inwardAt h := by
  have he : (fun v => imageEnergy 8 (sites v 0)) =
      fun v => 1-kernelD .value 0 + (4*kernelD .value v-2*kernelD .value (2*v))/3 +
        curvatureAt .value v := by
    funext v
    rw [energy_cross,curv_center .value v rfl]
    simp only [kernelD_value]
  have H (a n : ℝ) (hn : n=1 ∨ n=2) (ha : a=0 ∨ a=1/2) :
      HasDerivAt (fun v => kernelD .value (a+n*v)) (kernelD .first (a+n*h)*n) h := by
    have hv : a+n*h ∈ Ioo (-1:ℝ) 1 := by
      rcases hn with rfl|rfl <;> rcases ha with rfl|rfl <;>
        constructor <;> linarith [hh.1,hh.2]
    simpa using (kernelD_hasDerivAt .value (by decide) hv).comp h
      (((hasDerivAt_id' h).const_mul n).const_add a)
  have H₁ := H 0 1 (Or.inl rfl) (Or.inl rfl)
  have H₂ := H 0 2 (Or.inr rfl) (Or.inl rfl)
  have H₃ := H (1/2) 1 (Or.inl rfl) (Or.inr rfl)
  have H₄ := H (1/2) 2 (Or.inr rfl) (Or.inr rfl)
  simp only [zero_add,one_mul,mul_one] at H₁ H₂ H₃
  have hp := (hasDerivAt_const h (1-kernelD .value 0)).add
    (((H₁.const_mul 4).sub (H₂.const_mul 2)).div_const 3)
  have hq := (((hasDerivAt_const h (3*kernelD .value (1/2))).sub (H₃.const_mul 4)).add
    (H₄.const_mul 2)).div_const 3
  have hodd (v : ℝ) : kernelD .first (1/2-v) = -kernelD .first (1/2+v) := by
    rw [show 1/2-v = 1-(1/2+v) by ring,kernelD_reflection]
    simp [parity]
  rw [he]
  unfold curvatureAt inwardAt
  have hd := (hp.add hq).deriv
  simp only [Pi.add_apply,Pi.sub_apply] at hd
  change deriv (fun v : ℝ => 1-kernelD .value 0 + (4*kernelD .value v-2*kernelD .value (2*v))/3 +
    (3*kernelD .value (1/2)-4*kernelD .value (1/2+v)+2*kernelD .value (1/2+2*v))/3) h = _ at hd
  rw [hd]
  rw [hodd,hodd]
  ring

end GaussianChains.Bifurcation.Images
