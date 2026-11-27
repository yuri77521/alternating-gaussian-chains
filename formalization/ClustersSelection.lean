import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The discrete split, signed quadratic Taylor coefficient and selection
estimates used in the proof of Theorem 1. Coordinates in this file are angular. -/
noncomputable section

open Finset
open scoped BigOperators

namespace GaussianChains.Clusters

/-- Cost of the leading quadratic term for two packed odd blocks of sizes
`2*k+1` and `2*l+1`. -/
def splitCost (k l : ℕ) : ℕ := k*(k+1) + l*(l+1)

theorem balanced_split_cost {k l : ℕ} (hk : k ≤ l+1) (hl : l ≤ k+1) :
    splitCost k l = (k+l+1)^2 / 2 := by
  rcases le_total k l with h | h
  · have h' : l = k ∨ l = k+1 := by omega
    rcases h' with h' | h'
    · subst_vars
      have eq (u : ℕ) : (u+u+1)^2 = 2*splitCost u u + 1 := by unfold splitCost; ring
      have := eq l
      omega
    · subst l
      have eq : (k+(k+1)+1)^2 = 2*splitCost k (k+1) := by unfold splitCost; ring
      omega
  · have h' : k = l ∨ k = l+1 := by omega
    rcases h' with h' | h'
    · subst_vars
      have eq (u : ℕ) : (u+u+1)^2 = 2*splitCost u u + 1 := by unfold splitCost; ring
      have := eq l
      omega
    · subst k
      have eq : (l+1+l+1)^2 = 2*splitCost (l+1) l := by unfold splitCost; ring
      omega

theorem unbalanced_split_cost {k l : ℕ} (h : k+2 ≤ l ∨ l+2 ≤ k) :
    (k+l+1)^2 / 2 + 2 ≤ splitCost k l := by
  suffices (k+l+1)^2 + 3 ≤ 2*splitCost k l by omega
  rcases h with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold splitCost
    nlinarith only [Nat.zero_le (t^2), Nat.zero_le t]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold splitCost
    nlinarith only [Nat.zero_le (t^2), Nat.zero_le t]

/-- Cross-block ordered quadratic sum after normalizing the initial signs of
both odd blocks. The sites are arbitrary offsets, including negative offsets. -/
theorem cross_quadratic {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x : α → ℝ) (y : β → ℝ)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1) :
    ∑ i, ∑ j, w i * v j * (x i-y j)^2 =
      ((∑ i, w i*(x i)^2) - (∑ i, w i*x i)^2) +
      ((∑ j, v j*(y j)^2) - (∑ j, v j*y j)^2) +
      ((∑ i, w i*x i) - ∑ j, v j*y j)^2 := by
  classical
  have row (i : α) : ∑ j, w i * v j * (x i-y j)^2 =
      w i*(x i)^2 - (w i*x i)*(2*(∑ j, v j*y j)) +
        w i*(∑ j, v j*(y j)^2) := by
    calc
      _ = ∑ j, ((w i*(x i)^2)*v j - (2*(w i*x i))*(v j*y j) +
          w i*(v j*(y j)^2)) := by apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
                       ← mul_sum, hv]; ring
  simp_rw [row]
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, hw]
  ring

theorem within_quadratic {α : Type*} [Fintype α] (w x : α → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i*w j*(x i-x j)^2 =
      2*((∑ i, w i*(x i)^2) - (∑ i, w i*x i)^2) := by
  rw [cross_quadratic w w x x hw hw]
  ring

/-- The small angular floor absorbs the fourth-order Taylor error uniformly
in the number of sites. -/
theorem fourth_error_at_small_floor {N C η : ℝ} (hN : 0 < N) (hC : 0 < C)
    (hη : 0 ≤ η) (hsmall : η ≤ 1/(N*C^2)) :
    4/3*N^2*C^4*η^4 ≤ 4/3*η^2 := by
  have h1 := (le_div_iff₀ (show 0 < N*C^2 by positivity)).mp hsmall
  have h2 : (η*(N*C^2))^2 ≤ 1^2 := by gcongr
  calc
    _ = (4/3*η^2)*(η*(N*C^2))^2 := by ring
    _ ≤ (4/3*η^2)*1^2 := by gcongr
    _ = _ := by ring

/-- Equation (5) and the trial upper bound exclude every unbalanced split. -/
theorem split_of_taylor_bound {k l : ℕ} {N C η D V₀ Vπ Kπ Δ R F : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hη : 0 < η) (hsmall : η ≤ 1/(N*C^2))
    (hD : 2 ≤ D) (hK : 0 ≤ Kπ)
    (hV : (splitCost k l : ℝ)*η^2 ≤ V₀+Vπ)
    (hR : |R| ≤ 4/3*N^2*C^4*η^4)
    (hexp : F = D*(V₀+Vπ) + Kπ*Δ^2 + R)
    (htrial : F ≤ D*((((k+l+1)^2 / 2 : ℕ) : ℝ)*η^2)) :
    k ≤ l+1 ∧ l ≤ k+1 := by
  by_contra h
  have hu : k+2 ≤ l ∨ l+2 ≤ k := by omega
  have hc : ((((k+l+1)^2/2 : ℕ) : ℝ)+2) ≤ (splitCost k l : ℝ) := by
    exact_mod_cast unbalanced_split_cost hu
  have hR' := (neg_abs_le R).trans' (neg_le_neg
    (hR.trans (fourth_error_at_small_floor hN hC hη.le hsmall)))
  have hv := (mul_le_mul_of_nonneg_right hc (sq_nonneg η)).trans hV
  have haug := mul_le_mul_of_nonneg_left hv (show 0 ≤ D by linarith)
  have hpen := mul_nonneg hK (sq_nonneg Δ)
  nlinarith only [hR', hexp, htrial, haug, hpen,
    mul_le_mul_of_nonneg_right hD (sq_nonneg η), sq_pos_of_pos hη]

/-- At a slack gap the leading first derivative strictly dominates the
third-order Taylor error at the quantified small floor. -/
theorem gap_derivative_margin {N C η D : ℝ} (hN : 0 < N) (hC : 1 ≤ C)
    (hη : 0 < η) (hsmall : η ≤ 1/(N*C^2)) (hD : 2 ≤ D) :
    0 < 2*D*η - 8/3*N^2*C^3*η^3 := by
  have hC' : 0 < C := by linarith
  have h1 := (le_div_iff₀ (show 0 < N*C^2 by positivity)).mp hsmall
  have h2 : (η*(N*C^2))^2 ≤ 1^2 := by gcongr
  have h3 : N^2*C^3*η^3 ≤ η := by
    calc
      _ ≤ N^2*C^3*η^3 * C := le_mul_of_one_le_right (by positivity) hC
      _ = η*(η*(N*C^2))^2 := by ring
      _ ≤ η*1^2 := mul_le_mul_of_nonneg_left h2 hη.le
      _ = _ := by ring
  nlinarith only [h3, mul_le_mul_of_nonneg_right hD hη.le, hη]

/-- A local minimum with all sufficiently small variations of one slack gap
available cannot have the positive derivative in the contact argument. -/
theorem no_slack_local_min {f : ℝ → ℝ} {a f' N C η D : ℝ}
    (hN : 0 < N) (hC : 1 ≤ C) (hη : 0 < η) (hsmall : η ≤ 1/(N*C^2))
    (hD : 2 ≤ D) (hf : HasDerivAt f f' a)
    (hl : 2*D*η-8/3*N^2*C^3*η^3 ≤ f') : ¬ IsLocalMin f a := by
  intro hm
  have hz := hm.hasDerivAt_eq_zero hf
  linarith [gap_derivative_margin hN hC hη hsmall hD]

theorem midpoint_curvature_margin {Kπ C : ℝ} (hK : 5/6 ≤ Kπ) (hC : 2 ≤ C) :
    0 < 2*Kπ - 2/C^2 := by
  have hC' : 0 < C := by linarith
  have h2 : 2/C^2 ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hC')).mpr
    nlinarith
  linarith

/-- Reflection symmetry and the strict curvature bound select exactly zero
on the full feasible symmetric segment. -/
theorem midpoint_eq_zero_of_min {f : ℝ → ℝ} {r v Kπ C : ℝ}
    (hv : v ∈ Set.Icc (-r) r) (heven : f (-v) = f v)
    (hf : ContinuousOn f (Set.Icc (-r) r))
    (hK : 5/6 ≤ Kπ) (hC : 2 ≤ C)
    (hcurv : ∀ z ∈ interior (Set.Icc (-r) r),
      2*Kπ-2/C^2 ≤ deriv (deriv f) z)
    (hmin : f v ≤ f 0) : v = 0 := by
  have hc := strictConvexOn_of_deriv2_pos (convex_Icc (-r) r) hf
    (fun z hz => lt_of_lt_of_le (midpoint_curvature_margin hK hC) (hcurv z hz))
  by_contra hn
  have hne : v ≠ -v := by intro e; apply hn; linarith
  have hm : -v ∈ Set.Icc (-r) r := ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have half : (0 : ℝ) < 1/2 := by norm_num
  have hh := hc.2 (x := v) (y := -v) hv hm hne half half (by norm_num)
  simp only [smul_eq_mul, heven] at hh
  rw [show (1/2:ℝ)*v+(1/2)*(-v) = 0 by ring] at hh
  linarith


/-- The signed ordered cross interaction, in the coordinate charts based at a
pair of antipodes. The periodic kernel is evaluated at `c + x i - y j`. -/
def blockSum {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x : α → ℝ) (y : β → ℝ) (K : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, w i*v j*K (c+(x i-y j))

/-- A finite signed two-block kernel sum inherits a uniform scalar Taylor
bound with exactly one error allowance per ordered pair. -/
theorem block_remainder {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x : α → ℝ) (y : β → ℝ) (K : ℝ → ℝ)
    (c d ε : ℝ) (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hw' : ∀ i, |w i|=1) (hv' : ∀ j, |v j|=1)
    (h : ∀ i j, |K (c+(x i-y j))-K c-d/2*(x i-y j)^2| ≤ ε) :
    |blockSum w v x y K c - K c - d/2*(∑ i, ∑ j, w i*v j*(x i-y j)^2)| ≤
      (Fintype.card α : ℝ)*(Fintype.card β : ℝ)*ε := by
  classical
  let r := fun i j => w i*v j*(K (c+(x i-y j))-K c-d/2*(x i-y j)^2)
  have hr (i : α) (j : β) : |r i j| ≤ ε := by simpa [r, abs_mul, hw', hv'] using h i j
  have hsum : ∑ i, ∑ j, r i j =
      blockSum w v x y K c - K c - d/2*(∑ i, ∑ j, w i*v j*(x i-y j)^2) := by
    have hc : ∑ i, ∑ j, w i*v j*K c = K c := by
      simp [← sum_mul, ← mul_sum, hv, hw]
    rw [← hc] -- retain the scalar term below by first expanding the residual
    unfold blockSum
    rw [mul_sum]
    simp_rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    dsimp [r]
    ring
  rw [← hsum]
  calc
    _ ≤ ∑ i, |∑ j, r i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |r i j| := sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : α, ∑ _j : β, ε := sum_le_sum fun i _ => sum_le_sum fun j _ => hr i j
    _ = _ := by simp; ring

/-- The equation-(5) Taylor estimate for a pair of localized odd blocks.
All four ordered block interactions count, with minus signs on the two
within-block contributions. The kernel remainder `ε` is per ordered pair. -/
theorem two_block_taylor {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (x : α → ℝ) (y : β → ℝ) (K : ℝ → ℝ)
    (d₀ dπ ε : ℝ) (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hw' : ∀ i, |w i|=1) (hv' : ∀ j, |v j|=1)
    (h₀ : ∀ i j, |K (0+(x i-x j))-K 0-d₀/2*(x i-x j)^2| ≤ ε)
    (h₁ : ∀ i j, |K (0+(y i-y j))-K 0-d₀/2*(y i-y j)^2| ≤ ε)
    (hπ : ∀ i j, |K (Real.pi+(x i-y j))-K Real.pi-dπ/2*(x i-y j)^2| ≤ ε) :
    let P₀ := ∑ i, w i*x i
    let Pπ := ∑ i, v i*y i
    let V₀ := (∑ i, w i*(x i)^2)-P₀^2
    let Vπ := (∑ i, v i*(y i)^2)-Pπ^2
    let F := 2*(K 0 - K Real.pi) - blockSum w w x x K 0 - blockSum v v y y K 0 +
      2*blockSum w v x y K Real.pi
    |F - ((dπ-d₀)*(V₀+Vπ) + dπ*(P₀-Pπ)^2)| ≤
      ((Fintype.card α : ℝ)+(Fintype.card β : ℝ))^2*ε := by
  dsimp only
  have hxx := block_remainder w w x x K 0 d₀ ε hw hw hw' hw' h₀
  have hyy := block_remainder v v y y K 0 d₀ ε hv hv hv' hv' h₁
  have hxy := block_remainder w v x y K Real.pi dπ ε hw hv hw' hv' hπ
  rw [within_quadratic w x hw] at hxx
  rw [within_quadratic v y hv] at hyy
  rw [cross_quadratic w v x y hw hv] at hxy
  rw [abs_le] at hxx hyy hxy ⊢
  constructor <;> linarith [hxx.1,hxx.2,hyy.1,hyy.2,hxy.1,hxy.2]


private theorem primitive_bound_right (f d : ℝ → ℝ) (M : ℝ) (n : ℕ)
    (hf : ∀ t, HasDerivAt f (d t) t)
    (hd : ∀ t : ℝ, 0 ≤ t → |d t| ≤ M*t^n) (hf₀ : f 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    |f t| ≤ (M/(n+1))*t^(n+1) := by
  let G (z : ℝ) := (M/(n+1))*z^(n+1)
  have hG (z : ℝ) : HasDerivAt G (M*z^n) z := by
    have h := ((hasDerivAt_id z).pow (n+1)).const_mul (M/(n+1))
    convert h using 1 <;> simp [G, mul_assoc] <;> field_simp
  have hm (g g' : ℝ → ℝ) (hg : ∀ z, HasDerivAt g (g' z) z)
      (hp : ∀ z : ℝ, 0 ≤ z → 0 ≤ g' z) : g 0 ≤ g t := by
    have hmo : MonotoneOn g (Set.Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
        (fun z _ => (hg z).continuousAt.continuousWithinAt)
        (fun z _ => (hg z).hasDerivWithinAt)
        (fun z hz => hp z (interior_subset hz))
    exact hmo Set.self_mem_Ici ht ht
  have hsub := hm (fun z => G z - f z) (fun z => M*z^n-d z)
    (fun z => (hG z).sub (hf z)) (fun z hz => sub_nonneg.mpr ((le_abs_self _).trans (hd z hz)))
  have hadd := hm (fun z => G z + f z) (fun z => M*z^n+d z)
    (fun z => (hG z).add (hf z)) (fun z hz => by linarith [(abs_le.mp (hd z hz)).1])
  have h00 : G 0 = 0 := by simp [G]
  rw [abs_le]
  change -(G t) ≤ f t ∧ f t ≤ G t
  constructor <;> linarith only [hsub,hadd,h00,hf₀]

/-- Integrating a power majorant from zero gives the exact factorial
coefficient, on either side of the center. -/
theorem primitive_abs_bound (f d : ℝ → ℝ) (M : ℝ) (n : ℕ)
    (hf : ∀ t, HasDerivAt f (d t) t)
    (hd : ∀ t, |d t| ≤ M*|t|^n) (hf₀ : f 0 = 0) (t : ℝ) :
    |f t| ≤ M/(n+1)*|t|^(n+1) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact primitive_bound_right f d M n hf (fun z hz => by simpa [abs_of_nonneg hz] using hd z) hf₀ ht
  · have h := primitive_bound_right (fun z => f (-z)) (fun z => -d (-z)) M n
      (fun z => by simpa using (hf (-z)).comp z (hasDerivAt_id z).neg)
      (fun z hz => by simpa [abs_of_nonneg hz] using hd (-z))
      (by simpa) (neg_nonneg.mpr ht)
    simpa [abs_of_nonpos ht] using h

end GaussianChains.Clusters

