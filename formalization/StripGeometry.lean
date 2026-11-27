import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Slack coordinates for the six-site simplex and the support chart of Appendix A. -/
noncomputable section
namespace GaussianChains.Strip

abbrev Gaps := Fin 6 → ℝ

def simplex (u : Gaps) : Prop := (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1

def gapVector (h : ℝ) (g : Gaps) : Prop := (∀ i, h ≤ g i) ∧ ∑ i, g i = 1

def pack (h : ℝ) (u : Gaps) : Gaps := fun i => h + (1-6*h)*u i
def slack (h : ℝ) (g : Gaps) : Gaps := fun i => (g i-h)/(1-6*h)

theorem pack_sum (h : ℝ) {u : Gaps} (hu : simplex u) : ∑ i, pack h u i = 1 := by
  simp [pack, Finset.sum_add_distrib, ← Finset.mul_sum, hu.2]

theorem pack_feasible {h : ℝ} (hh : h ≤ 1/6) {u : Gaps} (hu : simplex u) :
    gapVector h (pack h u) := by
  refine ⟨fun i => ?_, pack_sum h hu⟩
  exact le_add_of_nonneg_right (mul_nonneg (by linarith) (hu.1 i))

theorem slack_simplex {h : ℝ} (hh : h < 1/6) {g : Gaps} (hg : gapVector h g) :
    simplex (slack h g) := by
  have hS : 0 < 1-6*h := by linarith
  refine ⟨fun i => div_nonneg (sub_nonneg.mpr (hg.1 i)) hS.le, ?_⟩
  simp [slack, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib, hg.2, hS.ne']

theorem pack_slack {h : ℝ} (hh : h < 1/6) (g : Gaps) : pack h (slack h g) = g := by
  have hs : 1-6*h ≠ 0 := ne_of_gt (by linarith)
  funext i
  dsimp [pack, slack]
  rw [mul_div_cancel₀ _ hs]
  ring

theorem slack_positive_iff {h : ℝ} (hh : h < 1/6) (g : Gaps) (i : Fin 6) :
    0 < slack h g i ↔ h < g i := by
  rw [slack, div_pos_iff_of_pos_right (by linarith), sub_pos]

/-- The endpoint is the singleton uniform gap vector, even though the slack parameterization
is no longer injective there. -/
theorem uniform_endpoint {g : Gaps} (hg : gapVector (1/6) g) :
    ∀ i, g i = 1/6 := by
  have hsum : ∑ i, (g i - 1/6) = 0 := by
    rw [Finset.sum_sub_distrib, hg.2]; norm_num
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => sub_nonneg.mpr (hg.1 i))).mp hsum
  intro i
  exact sub_eq_zero.mp (hz i (Finset.mem_univ i))

/-- At a tied maximum either choice of the distinguished coordinate is legitimate. -/
theorem exists_distinguished (u : Gaps) : ∃ k, ∀ j, u j ≤ u k := by
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  exact ⟨k, fun j => hk j (Finset.mem_univ _)⟩

theorem free_coordinate_le_half {u : Gaps} (hu : simplex u) {a b : Fin 6}
    (hne : a ≠ b) (hmax : u a ≤ u b) : u a ≤ 1/2 := by
  have hsub : ({a,b} : Finset (Fin 6)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hu.1 i)
  rw [Finset.sum_pair hne, hu.2] at hpair
  linarith

/-- Transfer in the *original* simplex, keeping all other coordinates fixed.
No chosen-largest condition is imposed on the variation. -/
def transfer (u : Gaps) (a b : Fin 6) (t : ℝ) : Gaps :=
  fun i => u i + (if i = a then t else 0) - (if i = b then t else 0)

theorem transfer_simplex {u : Gaps} (hu : simplex u) {a b : Fin 6} (hab : a ≠ b)
    {t : ℝ} (ha : -u a ≤ t) (hb : t ≤ u b) : simplex (transfer u a b t) := by
  refine ⟨fun i => ?_, ?_⟩
  · by_cases ia : i = a
    · subst i; simp [transfer, hab]; linarith
    · by_cases ib : i = b
      · subst i; simp [transfer, ia, hb]
      · simp [transfer, ia, ib, hu.1]
  · simp [transfer, Finset.sum_sub_distrib, Finset.sum_add_distrib, hu.2]

theorem transfer_two_sided {u : Gaps} (hu : simplex u) {a b : Fin 6} (hab : a ≠ b)
    (ha : 0 < u a) (hb : 0 < u b) :
    ∃ ε > (0 : ℝ), ∀ t, |t| ≤ ε → simplex (transfer u a b t) := by
  refine ⟨min (u a) (u b), lt_min ha hb, fun t ht => ?_⟩
  have hh := abs_le.mp ht
  exact transfer_simplex hu hab (le_trans (neg_le_neg (min_le_left _ _)) hh.1)
    (hh.2.trans (min_le_right _ _))

end GaussianChains.Strip
