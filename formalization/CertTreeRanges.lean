import CertTree
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Sound sparse range queries on closed nearest-node cells. A query at either
endpoint uses the same rounded node as the table generator. -/
namespace GaussianChains.Cert.Tables
open Interval

def hull (A B : Interval) : Interval := ⟨min A.lo B.lo, max A.hi B.hi⟩

theorem hull_left {A B : Interval} {x : ℝ} (h : A.Mem x) : (hull A B).Mem x := by
  exact ⟨(show ((hull A B).lo : ℝ) ≤ A.lo by exact_mod_cast min_le_left A.lo B.lo).trans h.1,
    h.2.trans (by exact_mod_cast le_max_left A.hi B.hi)⟩

theorem hull_right {A B : Interval} {x : ℝ} (h : B.Mem x) : (hull A B).Mem x := by
  exact ⟨(show ((hull A B).lo : ℝ) ≤ B.lo by exact_mod_cast min_le_right A.lo B.lo).trans h.1,
    h.2.trans (by exact_mod_cast le_max_right A.hi B.hi)⟩

/-- Entry at level j, covering 2^j consecutive nodes. -/
def sparse (node : ℕ → Interval) : ℕ → ℕ → Interval
  | 0, base => node base
  | j+1, base => hull (sparse node j base) (sparse node j (base + 2^j))

theorem sparse_mem (node : ℕ → Interval) (j base p : ℕ) (hp : base ≤ p)
    (hp' : p < base + 2^j) {x : ℝ} (hx : (node p).Mem x) :
    (sparse node j base).Mem x := by
  induction j generalizing base with
  | zero =>
    have h : p = base := by simp only [pow_zero] at hp'; omega
    simpa [sparse, ← h] using hx
  | succ j ih =>
    rw [pow_succ] at hp'
    by_cases h : p < base+2^j
    · exact hull_left (ih _ hp h)
    · exact hull_right (ih _ (by omega) (by omega))

def rangeHull (node : ℕ → Interval) (first last : ℕ) : Interval :=
  let level := (last + 1 - first).log2
  hull (sparse node level first) (sparse node level (last + 1 - 2^level))

theorem rangeHull_mem {node : ℕ → Interval} {first last p : ℕ} (hl : first ≤ p) (hr : p ≤ last)
    {x : ℝ} (hx : (node p).Mem x) : (rangeHull node first last).Mem x := by
  let n := last + 1 - first
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hlow := Nat.log2_self_le hn
  have hhi := Nat.lt_log2_self (n := n)
  rw [pow_succ] at hhi
  unfold rangeHull
  change (hull (sparse node n.log2 first) (sparse node n.log2 (last + 1 - 2^n.log2))).Mem x
  by_cases h : p < first + 2^n.log2
  · exact hull_left (sparse_mem node _ _ p hl h hx)
  · have he : n + first = last+1 := by dsimp [n]; omega
    exact hull_right (sparse_mem node _ _ p (by omega) (by omega) hx)

def nearest (M : ℕ+) (q : ℚ) := ⌊(M:ℚ)*q + 1/2⌋.toNat

noncomputable def nearestReal (M : ℕ+) (x : ℝ) := ⌊(M:ℝ)*x + 1/2⌋.toNat

theorem nearest_cast (M : ℕ+) (q : ℚ) : nearestReal M (q:ℝ) = nearest M q := by
  unfold nearestReal nearest
  congr 1
  convert Rat.floor_cast (α:=ℝ) ((M:ℚ)*q+1/2) using 2; push_cast; rfl

theorem nearestReal_mono (M : ℕ+) : Monotone (nearestReal M) := by
  intro a b hab
  apply Int.toNat_le_toNat
  exact Int.floor_mono (add_le_add (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg (M:ℕ))) le_rfl)

theorem nearest_bound {M : ℕ+} {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    nearestReal M x ≤ (M:ℕ) ∧ |x - ((nearestReal M x : ℕ):ℝ)/M| ≤ 1/(2*(M:ℝ)) := by
  let z := (M:ℝ)*x+1/2
  have hm : (0:ℝ) < M := by exact_mod_cast M.2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hcast : ((nearestReal M x : ℕ):ℝ) = (⌊z⌋:ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hz)
  have hlo := Int.floor_le z
  have hhi := Int.lt_floor_add_one z
  have hl : ⌊z⌋ ≤ (M:ℤ) := by
    apply Int.floor_le_iff.mpr
    dsimp [z]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hx1 hm.le]
  constructor
  · exact_mod_cast (Int.toNat_le_toNat hl)
  · rw [hcast, abs_le]
    constructor <;> field_simp <;> dsimp [z] at hlo hhi <;> linarith

def pad (I : Interval) (e : ℚ) : Interval := ⟨I.lo-e, I.hi+e⟩

theorem pad_mem {I : Interval} {x y : ℝ} {e : ℚ} (hy : I.Mem y) (h : |x-y| ≤ (e:ℝ)) :
    (pad I e).Mem x := by
  unfold pad Interval.Mem
  push_cast
  rcases abs_le.mp h with ⟨hl,hu⟩
  constructor <;> linarith [hy.1,hy.2]

/-- The optional output grid corresponds to rounding the extension up in units
of (1/unit), matching the sampled strip table. -/
def paddedNode (M unit : ℕ+) (cap : ℚ) (node : ℕ → Interval) (p : ℕ) : Interval :=
  let e : ℚ := (⌈cap/(2*(M:ℚ))*(unit:ℚ)⌉ : ℚ) / unit
  pad (node p) e

theorem paddedNode_mem {f : ℝ → ℝ} {cap : ℚ} (hc : 0 ≤ cap)
    (hd : Differentiable ℝ f) (hcap : ∀ y, |deriv f y| ≤ (cap:ℝ))
    (M unit : ℕ+) {node : ℕ → Interval} (hn : ∀ p ≤ (M:ℕ), (node p).Mem (f ((p:ℝ)/M)))
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (paddedNode M unit cap node (nearestReal M x)).Mem (f x) := by
  obtain ⟨hp,hp'⟩ := nearest_bound (M:=M) hx hx1
  have hdif := Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=f) (s:=Set.univ) (fun y _ => hd y)
    (fun y _ => by simpa only [Real.norm_eq_abs] using hcap y) convex_univ
    (Set.mem_univ (((nearestReal M x:ℕ):ℝ)/M)) (Set.mem_univ x)
  simp only [Real.norm_eq_abs] at hdif
  apply pad_mem (hn _ hp)
  have hround : cap/(2*(M:ℚ)) ≤ (⌈cap/(2*(M:ℚ))*(unit:ℚ)⌉:ℚ)/unit :=
    (le_div_iff₀ (show (0:ℚ) < unit by exact_mod_cast unit.2)).mpr (Int.le_ceil _)
  have h := hdif.trans (mul_le_mul_of_nonneg_left hp' (by exact_mod_cast hc))
  rw [mul_one_div] at h
  exact h.trans (by exact_mod_cast hround)

def spatialRange (M unit : ℕ+) (cap : ℚ) (node : ℕ → Interval) (left right : ℚ) : Interval :=
  rangeHull (paddedNode M unit cap node) (nearest M left) (nearest M right)

/-- Whole-interval evaluation, including the query endpoints and nearest-node ties. -/
theorem spatialRange_mem {f : ℝ → ℝ} {cap : ℚ} (hc : 0 ≤ cap)
    (hd : Differentiable ℝ f) (hcap : ∀ y, |deriv f y| ≤ (cap:ℝ))
    (M unit : ℕ+) {node : ℕ → Interval} (hn : ∀ p ≤ (M:ℕ), (node p).Mem (f ((p:ℝ)/M)))
    {left right : ℚ} (hl : 0 ≤ left) (hr : right ≤ 1)
    {x : ℝ} (hx : (left:ℝ) ≤ x ∧ x ≤ (right:ℝ)) :
    (spatialRange M unit cap node left right).Mem (f x) := by
  apply rangeHull_mem (p:=nearestReal M x)
  · rw [← nearest_cast]; exact nearestReal_mono M hx.1
  · rw [← nearest_cast]; exact nearestReal_mono M hx.2
  · exact paddedNode_mem hc hd hcap M unit hn
      ((show (0:ℝ) ≤ left by exact_mod_cast hl).trans hx.1)
      (hx.2.trans (by exact_mod_cast hr))

end GaussianChains.Cert.Tables
