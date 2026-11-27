import BandTree

/-! Real semantics of the interval tests used in a strip tree. The 15 ordered
index choices i<j appear exactly once. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Finset Interval

abbrev Pair := Fin 6 × Fin 6
def pairs : Finset Pair := univ.filter fun (p : Pair) => p.1 < p.2

def distance (h : ℝ) (u : Fin 6 → ℝ) (p : Pair) : ℝ :=
  ((p.2.val-p.1.val:ℕ):ℝ)*h + (1-6*h)*(∑ k ∈ arc p.1 p.2, u k)

def coefficient (p : Pair) : ℚ := (-1:ℚ)^p.1.val * (-1:ℚ)^p.2.val

def crosses (p : Pair) (k : Fin 6) : ℤ :=
  if p.1 ≤ k ∧ k < p.2 then 1 else 0

def order : Terminal → ℕ
  | .value => 0
  | .gradient _ => 1
  | .curvature _ _ => 2

def weight (r : Terminal) (p : Pair) : ℚ :=
  coefficient p * match r with
    | .value => 1
    | .gradient k => (crosses p k.castSucc : ℚ)
    | .curvature i j => ((crosses p i - crosses p j : ℤ) : ℚ)^2

def expression (r : Terminal) (F : ℕ → ℝ → ℝ) (h : ℝ) (u : Fin 6 → ℝ) : ℝ :=
  ∑ p ∈ pairs, (weight r p : ℝ) * F (order r) (distance h u p)

theorem distance_unit {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1/6)
    {u : Fin 6 → ℝ} (hs : simplex u) (p : Pair) :
    0 ≤ distance h u p ∧ distance h u p ≤ 1 := by
  have h0 : 0 ≤ ∑ k ∈ arc p.1 p.2, u k := sum_nonneg (fun i _ => hs.1 i)
  have h1 : (∑ k ∈ arc p.1 p.2, u k) ≤ 1 := by
    rw [← hs.2]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hs.1 i)
  have hw : 0 ≤ 1 - 6*h := by linarith
  have hn : ((p.2.val-p.1.val:ℕ):ℝ) ≤ 6 := by
    exact_mod_cast (show p.2.val-p.1.val ≤ 6 by have := p.2.isLt; omega)
  unfold distance
  constructor
  · positivity
  · have hu := mul_le_mul_of_nonneg_left h1 hw
    linarith [mul_le_mul_of_nonneg_right hn hh]

abbrev Oracle := ℕ → Interval → Interval

def enclosure (q : Oracle) (floor : Interval) (B : Box 6) (r : Terminal) : Interval :=
  sumRange pairs (fun p => (singleton (weight r p)).mul
    (q (order r) (pairRange floor B p.1 p.2)))

theorem enclosure_sound {F : ℕ → ℝ → ℝ} {q : Oracle}
    (hq : ∀ r : Terminal, ∀ I x, I.Mem x → 0 ≤ x → x ≤ 1 → (q (order r) I).Mem (F (order r) x))
    {h : ℝ} {u : Fin 6 → ℝ} {floor : Interval} {B : Box 6}
    (hh : floor.Mem h) (h0 : 0 ≤ h) (h6 : h ≤ 1/6) (hu : B.Mem u) (hs : simplex u) (r : Terminal) :
    (enclosure q floor B r).Mem (expression r F h u) := by
  exact sumRange_mem fun p _ => mul_mem (singleton_mem (weight r p))
    (hq r _ _ (pairRange_mem hh hu hs.2 p.1 p.2) (distance_unit h0 h6 hs p).1 (distance_unit h0 h6 hs p).2)

/-- The trial allocation has only the two opposite slack gaps. -/
def trial (j : Fin 5) (i : Fin 6) : ℚ :=
  if i = 2 then (j.val:ℚ)/8 else if i = 5 then 1 - (j.val:ℚ)/8 else 0

theorem trial_simplex (j : Fin 5) : simplex (fun i => (trial j i : ℝ)) := by
  have cert : ∀ t : Fin 5, (∀ i, 0 ≤ trial t i) ∧ (∑ i, trial t i) = 1 := by decide +kernel
  constructor
  · intro i
    change (0 : ℝ) ≤ (trial j i : ℝ)
    exact_mod_cast (cert j).1 i
  · change (∑ i : Fin 6, (trial j i : ℝ)) = 1
    exact_mod_cast (cert j).2

def trialBox (j : Fin 5) : Box 6 := fun i => singleton (trial j i)

def free (A : Support) (k : Fin 6) : Bool := decide (k = 5 ∨ ∃ i ∈ A, i.castSucc = k)

def testLeaf (q : Oracle) (floor : Interval) (A : Support) (j : Fin 5)
    (B : Box 6) (r : Terminal) : Bool :=
  let I := enclosure q floor B r
  match r with
  | .value => decide (I.hi < (enclosure q floor (trialBox j) .value).lo)
  | .gradient k => decide (k ∈ A ∧ (I.hi < 0 ∨ 0 < I.lo))
  | .curvature a b => free A a && free A b && decide (a ≠ b ∧ 0 < I.lo)

/-- Three necessary variational tests, in the normalized score (to be maximized). -/
def Stationary (A : Support) (j : Fin 5) (F : ℕ → ℝ → ℝ) (h : ℝ) (u : Fin 6 → ℝ) : Prop :=
  expression .value F h (fun i => (trial j i : ℝ)) ≤ expression .value F h u ∧
  (∀ k ∈ A, expression (.gradient k) F h u = 0) ∧
  ∀ a b, free A a = true → free A b = true → a ≠ b → expression (.curvature a b) F h u ≤ 0

theorem testLeaf_sound {F : ℕ → ℝ → ℝ} {q : Oracle}
    (hq : ∀ r : Terminal, ∀ I x, I.Mem x → 0 ≤ x → x ≤ 1 → (q (order r) I).Mem (F (order r) x))
    {h : ℝ} {u : Fin 6 → ℝ} {floor : Interval} {B : Box 6} {A : Support} {j : Fin 5}
    (hh : floor.Mem h) (h0 : 0 ≤ h) (h6 : h ≤ 1/6) (hb : B.Mem u) (hs : simplex u)
    (r : Terminal) (hr : testLeaf q floor A j B r = true) : ¬Stationary A j F h u := by
  intro hp
  have he := enclosure_sound hq hh h0 h6 hb hs r
  cases r with
  | value =>
    have ht := enclosure_sound hq hh h0 h6 (B := trialBox j) (fun i => singleton_mem (trial j i))
      (trial_simplex j) .value
    have hlt : (enclosure q floor B .value).hi < (enclosure q floor (trialBox j) .value).lo :=
      of_decide_eq_true hr
    exact (not_lt_of_ge (ht.1.trans (hp.1.trans he.2))) (by exact_mod_cast hlt)
  | gradient k =>
    have hc : k ∈ A ∧ ((enclosure q floor B (.gradient k)).hi < 0 ∨
        0 < (enclosure q floor B (.gradient k)).lo) := of_decide_eq_true hr
    rw [hp.2.1 k hc.1] at he
    rcases hc.2 with h | h
    · exact (not_lt_of_ge he.2) (by exact_mod_cast h)
    · exact (not_lt_of_ge he.1) (by exact_mod_cast h)
  | curvature a b =>
    simp only [testLeaf, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hnon := hp.2.2 a b hr.1.1 hr.1.2 hr.2.1
    exact (not_lt_of_ge (he.1.trans hnon)) (by exact_mod_cast hr.2.2)

end GaussianChains.Band
