import CertTree

namespace GaussianChains.PhaseStrip

open Cert

/-- Polynomial expressions on the nome and cosine coordinate. Integer
coefficients keep the same expression valid over reals and interval boxes. -/
inductive Expr where
  | q | x
  | c (v : ℤ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : ℕ)
  deriving Inhabited

namespace Expr
instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩
instance : HPow Expr ℕ Expr := ⟨.pow⟩
instance (n : ℕ) : OfNat Expr n := ⟨.c n⟩

noncomputable def eval (q x : ℝ) : Expr → ℝ
  | .q => q
  | .x => x
  | .c v => v
  | .add a b => eval q x a + eval q x b
  | .sub a b => eval q x a - eval q x b
  | .mul a b => eval q x a * eval q x b
  | .pow a n => eval q x a ^ n

abbrev grid : ℕ+ := ⟨10^32, by decide⟩
def product (A B : Interval) := (A.mul B).roundOut grid

private theorem product_mem {A B : Interval} {a b : ℝ} (ha : A.Mem a) (hb : B.Mem b) :
    (product A B).Mem (a*b) := Interval.roundOut_mem (Interval.mul_mem ha hb) _

def power (A : Interval) : ℕ → Interval
  | 0 => .singleton 1
  | n+1 => product (power A n) A

private theorem power_mem {A : Interval} {a : ℝ} (ha : A.Mem a) (n : ℕ) :
    (power A n).Mem (a^n) := by
  induction n with
  | zero => simpa [power] using Interval.singleton_mem 1
  | succ n ih => exact pow_succ a n ▸ product_mem ih ha

def box (Q X : Interval) : Expr → Interval
  | .q => Q
  | .x => X
  | .c v => .singleton v
  | .add a b => (box Q X a).add (box Q X b)
  | .sub a b => (box Q X a).add (box Q X b).neg
  | .mul a b => product (box Q X a) (box Q X b)
  | .pow a n => power (box Q X a) n

theorem box_mem {Q X : Interval} {q x : ℝ} (hQ : Q.Mem q) (hX : X.Mem x) (e : Expr) :
    (box Q X e).Mem (eval q x e) := by
  induction e with
  | q => exact hQ
  | x => exact hX
  | c n => simpa [box,eval] using Interval.singleton_mem (n:ℚ)
  | add a b ha hb => exact Interval.add_mem ha hb
  | sub a b ha hb => simpa only [eval, box, sub_eq_add_neg] using Interval.add_mem ha (Interval.neg_mem hb)
  | mul a b ha hb => exact product_mem ha hb
  | pow a n ha => exact power_mem ha n

@[simp] theorem eval_add (q x : ℝ) (a b : Expr) :
    (a+b).eval q x = a.eval q x + b.eval q x := rfl
@[simp] theorem eval_sub (q x : ℝ) (a b : Expr) :
    (a-b).eval q x = a.eval q x - b.eval q x := rfl
@[simp] theorem eval_mul (q x : ℝ) (a b : Expr) :
    (a*b).eval q x = a.eval q x * b.eval q x := rfl
@[simp] theorem eval_pow (q x : ℝ) (a : Expr) (n : ℕ) :
    (a^n).eval q x = a.eval q x ^ n := rfl
@[simp] theorem eval_num (q x : ℝ) (n : ℕ) :
    (OfNat.ofNat n : Expr).eval q x = n := by simp [eval]
end Expr

end GaussianChains.PhaseStrip

