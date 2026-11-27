import PhaseStripExpressions
import PackedFaceSlopes

namespace GaussianChains.PhaseStrip

open GaussianChains.Cert GaussianChains.PackedFace Polynomial Polynomial.Chebyshev

inductive SlopeKind where | value | dx | qdq
  deriving DecidableEq, Repr

private theorem eval_zero (q x : ℝ) : (0 : Expr).eval q x = 0 := by
  change ((0:ℤ):ℝ) = 0
  norm_num
private theorem eval_one (q x : ℝ) : (1 : Expr).eval q x = 1 := by
  change ((1:ℤ):ℝ) = 1
  norm_num
private theorem eval_two (q x : ℝ) : (2 : Expr).eval q x = 2 := by
  change ((2:ℤ):ℝ) = 2
  norm_num
attribute [local simp] eval_zero eval_one eval_two

noncomputable def zAt (outer : Bool) (x : ℝ) := if outer then 3*x-4*x^3 else 1
noncomputable def dzAt (outer : Bool) (x : ℝ) := if outer then 3-12*x^2 else 0

noncomputable def summand (kind : SlopeKind) (outer : Bool) (n : ℕ) (q x : ℝ) : ℝ :=
  match kind with
  | .value => endpointMode n q x (zAt outer x)
  | .dx => endpointDx n q x (zAt outer x) (dzAt outer x)
  | .qdq => q * endpointDq n q x (zAt outer x)

private def cheb (b : Bool) (u : Expr) : ℕ → Expr
  | 0 => 1
  | 1 => if b then 2*u else u
  | k+2 => 2*u*cheb b u (k+1) - cheb b u k

private theorem cheb_eval (b : Bool) (q x : ℝ) (u : Expr) (n : ℕ) :
    (cheb b u n).eval q x = (if b then U ℝ (n:ℤ) else T ℝ (n:ℤ)).eval (u.eval q x) := by
  induction n using Nat.twoStepInduction with
  | zero => cases b <;> simp [cheb]
  | one => cases b <;> simp [cheb]
  | more n h₀ h₁ =>
    cases b <;> simp [cheb, h₀, h₁, T_add_two, U_add_two]

private def du (u : Expr) : ℕ → Expr
  | 0 => 0
  | 1 => 2
  | k+2 => 2*cheb true u (k+1) + 2*u*du u (k+1) - du u k

private theorem du_eval (q x : ℝ) (u : Expr) (n : ℕ) :
    (du u n).eval q x = (U ℝ (n:ℤ)).derivative.eval (u.eval q x) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [du]
  | one => simp [du]
  | more n h₀ h₁ =>
    simp [du, h₀, h₁, cheb_eval, U_add_two, derivative_mul]

private def ze (outer : Bool) : Expr := if outer then 3*.x-4*(.x : Expr)^3 else 1
private def dze (outer : Bool) : Expr := if outer then 3-12*(.x : Expr)^2 else 0

private theorem ze_eval (b : Bool) (q x : ℝ) : (ze b).eval q x = zAt b x := by
  cases b <;> simp [ze,zAt,Expr.eval]
private theorem dze_eval (b : Bool) (q x : ℝ) : (dze b).eval q x = dzAt b x := by
  cases b <;> simp [dze,dzAt,Expr.eval]

/-- One positive frequency indexed by k = n-1. The T and U recurrences and
the differentiated U recurrence are shared by the value and both derivatives. -/
def modeExpr (kind : SlopeKind) (outer : Bool) (k : ℕ) : Expr :=
  let n := k+1
  let a := 2*cheb false .x n-1
  let u := cheb true (ze outer) k
  let w := (.c ((-1:ℤ)^(n+1)*n) : Expr) * (.q : Expr)^(n^2-1)
  match kind with
  | .value => w * a^2 * u
  | .qdq => .c ((n^2-1:ℕ):ℤ) * (w * a^2 * u)
  | .dx => w * (4*a*(.c n * cheb true .x k)*u + a^2*du (ze outer) k*dze outer)

private theorem scaled_q (k : ℕ) (q x z : ℝ) :
    q * endpointDq (k+1) q x z = ((((k+1)^2-1 : ℕ):ℝ)) * endpointMode (k+1) q x z := by
  cases k with
  | zero => simp [endpointDq]
  | succ k => exact endpointMode_scaled_q (by omega) _ _ _

theorem modeExpr_eval (kind : SlopeKind) (outer : Bool) (k : ℕ) (q x : ℝ) :
    (modeExpr kind outer k).eval q x = summand kind outer (k+1) q x := by
  cases kind <;>
    simp [modeExpr,summand,scaled_q,endpointMode,endpointDx, modeT, modeU,
      cheb_eval,du_eval,ze_eval,dze_eval,Expr.eval,T_derivative_eq_U]

def sixBox (kind : SlopeKind) (outer : Bool) (Q X : Interval) : Interval :=
  ⟨∑ k ∈ Finset.range 6, ((modeExpr kind outer k).box Q X).lo,
   ∑ k ∈ Finset.range 6, ((modeExpr kind outer k).box Q X).hi⟩

theorem sixBox_mem (kind : SlopeKind) (outer : Bool) {Q X : Interval} {q x : ℝ}
    (hQ : Q.Mem q) (hX : X.Mem x) :
    (sixBox kind outer Q X).Mem (∑ k ∈ Finset.range 6, summand kind outer (k+1) q x) := by
  have hv (k : ℕ) := Expr.box_mem hQ hX (modeExpr kind outer k)
  simp_rw [modeExpr_eval] at hv
  constructor
  · simpa [sixBox] using Finset.sum_le_sum (s := Finset.range 6) (fun k _ => (hv k).1)
  · simpa [sixBox] using Finset.sum_le_sum (s := Finset.range 6) (fun k _ => (hv k).2)

end GaussianChains.PhaseStrip

