import ChainScore
import ChainGeometry
import CertTreeVariations
import CertTreeKernelDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FinCases

/-! Derivative tests for transfers between slack gaps, on physical site coordinates.
The velocity of pair (i,j) is the difference of two cut indicators. -/
noncomputable section
namespace GaussianChains.Strip
open Filter Topology

def cut (k i : Fin 6) : ℤ := if k < i then 1 else 0
def speed (a b i : Fin 6) : ℤ := cut a i - cut b i

def move (x : Fin 6 → ℝ) (a b : Fin 6) (t : ℝ) (i : Fin 6) : ℝ :=
  x i + t*(speed a b i : ℝ)

private def nextSite (i : Fin 6) : Fin 6 := ⟨(i.val+1)%6, Nat.mod_lt _ (by decide)⟩

theorem cyclic_speed : ∀ a b i : Fin 6,
    speed a b (nextSite i) - speed a b i =
      (if i = a then 1 else 0) - (if i = b then 1 else 0) := by decide

/-- For i<j, only the physical pair separations crossing one of the two cuts change. -/
theorem cut_pair_speed : ∀ a b i j : Fin 6, i < j →
    speed a b j-speed a b i =
      (if i ≤ a ∧ a < j then 1 else 0)-(if i ≤ b ∧ b < j then 1 else 0) := by decide

theorem cut_pair_curvature : ∀ a b i j : Fin 6, i < j →
    (speed a b j-speed a b i)^2 =
      (if (i ≤ a ∧ a < j) ↔ (i ≤ b ∧ b < j) then 0 else 1) := by decide

theorem move_gap (x : Fin 6 → ℝ) (a b i : Fin 6) (t : ℝ) :
    gap (by decide) (move x a b t) i = gap (by decide) x i +
      (if i=a then t else 0) - (if i=b then t else 0) := by
  have hs := cyclic_speed a b i
  have hs' := congrArg (Int.cast : ℤ → ℝ) hs
  push_cast at hs'
  have hx : gap (by decide) (move x a b t) i =
      gap (by decide) x i + t*((speed a b (nextSite i) : ℝ) - (speed a b i : ℝ)) := by
    simp only [gap,liftSite,move,nextSite,Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt]
    ring
  rw [hx,hs']
  split_ifs <;> ring

theorem move_feasible {x : Fin 6 → ℝ} {h : ℝ} (hx : Feasible (by decide) h x) {a b : Fin 6}
    (hab : a ≠ b) (ha : h < gap (by decide) x a) (hb : h < gap (by decide) x b) :
    ∀ᶠ t in 𝓝 (0:ℝ), Feasible (by decide) h (move x a b t) := by
  let ε := min (gap (by decide) x a -h) (gap (by decide) x b -h)
  have he : 0 < ε := lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
  have hε : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioo (-ε) ε :=
    Ioo_mem_nhds (neg_lt_zero.mpr he) he
  filter_upwards [hε] with t ht
  intro i
  rw [move_gap]
  have hl := ht.1
  have hr := ht.2
  by_cases hia : i = a
  · subst i
    simp [hab]
    dsimp [ε] at hl
    linarith [min_le_left (gap (by decide) x a -h) (gap (by decide) x b -h)]
  · by_cases hib : i = b
    · subst i
      simp [hia]
      dsimp [ε] at hr
      linarith [min_le_right (gap (by decide) x a -h) (gap (by decide) x b -h)]
    · simpa [hia,hib] using hx i

private def coeff (i j : Fin 6) : ℝ := if i<j then charge i*charge j else 0

/-- Order p along a ray, in physical coordinates. For p=1 it is the signed cut sum;
for p=2 it is the sum over the symmetric difference of the cuts. -/
def raySum (p : ℕ) (F : ℝ → ℝ) (x : Fin 6 → ℝ) (a b : Fin 6) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, coeff i j * (((speed a b j : ℝ) - (speed a b i : ℝ))^p) *
    F (x j - x i + t*((speed a b j : ℝ) - (speed a b i : ℝ)))

theorem raySum_deriv (p : ℕ) {F D : ℝ → ℝ} (hF : ∀ z, HasDerivAt F (D z) z)
    (x : Fin 6 → ℝ) (a b : Fin 6) (t : ℝ) :
    HasDerivAt (raySum p F x a b) (raySum (p+1) D x a b t) t := by
  unfold raySum
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  let v := (speed a b j : ℝ) - (speed a b i : ℝ)
  have hl : HasDerivAt (fun t : ℝ => x j-x i+t*v) v t := by
    simpa using ((hasDerivAt_id t).mul_const v).const_add (x j-x i)
  have hd := ((hF _).comp t hl).const_mul (coeff i j*v^p)
  convert hd using 1 <;> dsimp [v,Function.comp_def] <;> ring

theorem raySum_pairScore (s : ℝ) (x : Fin 6 → ℝ) (a b : Fin 6) (t : ℝ) :
    raySum 0 (kernel s) x a b t = pairScore s (move x a b t) := by
  unfold pairScore raySum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i<j
  · simp only [coeff,if_pos hij,pow_zero,mul_one,move]
    congr 2
    ring
  · simp [coeff,hij]

/-- The analytical meaning of the gradient and curvature terminals at every tied or
untied pair of slack gaps. Derivative enclosures may now be supplied for D and D2. -/
theorem score_cut_conditions {s h : ℝ} (x : Fin 6 → ℝ) (hx : Feasible (by decide) h x)
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y)
    {D D2 : ℝ → ℝ} (hD : ∀ z, HasDerivAt (kernel s) (D z) z)
    (hD2 : ∀ z, HasDerivAt D (D2 z) z)
    {a b : Fin 6} (hab : a ≠ b) (ha : h < gap (by decide) x a) (hb : h < gap (by decide) x b) :
    raySum 1 D x a b 0 = 0 ∧ raySum 2 D2 x a b 0 ≤ 0 := by
  let f := raySum 0 (kernel s) x a b
  have hf (t : ℝ) := raySum_deriv 0 hD x a b t
  have hf' (t : ℝ) := raySum_deriv 1 hD2 x a b t
  have hmax : IsLocalMax f 0 := by
    filter_upwards [move_feasible hx hab ha hb] with t ht
    change raySum 0 (kernel s) x a b t ≤ raySum 0 (kernel s) x a b 0
    rw [raySum_pairScore, raySum_pairScore, show move x a b 0 = x by funext i; simp [move]]
    exact (imageEnergy_le_iff_pairScore_ge (by decide) s x _).mp (hmin _ ht)
  have cond := Cert.necessary_transfer hmax (hf 0).continuousAt
  have deq : deriv f = raySum 1 D x a b := funext fun t => (hf t).deriv
  rw [deq,(hf' 0).deriv] at cond
  exact cond

open ImageCalculus in
theorem gaussian_cut_conditions {s h : ℝ} (hs : 0 < s) (x : Fin 6 → ℝ)
    (hx : Feasible (by decide) h x)
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y)
    {a b : Fin 6} (hab : a ≠ b) (ha : h < gap (by decide) x a) (hb : h < gap (by decide) x b) :
    raySum 1 (periodized s (next s 1)) x a b 0 = 0 ∧
      raySum 2 (periodized s (next s (next s 1))) x a b 0 ≤ 0 := by
  apply score_cut_conditions x hx hmin _ (periodized_derivative hs (next s 1)) hab ha hb
  rw [kernel_periodized]
  exact periodized_derivative hs 1

#print axioms gaussian_cut_conditions
end GaussianChains.Strip
