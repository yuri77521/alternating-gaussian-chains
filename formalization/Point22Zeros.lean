import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! The six-zero obstruction in the interior of the six-site simplex. Angles
are lifted to an increasing sequence of seven endpoints spanning one turn;
the seventh endpoint closes the last arc. -/

namespace GaussianChains.Point22

open Set Polynomial

/-- Opposite endpoint signs give six distinct zeros, one in each open arc.
There is no double counting of the endpoints, even on the closing arc. -/
theorem six_distinct_zeros (T : ℝ → ℝ) (hT : Continuous T) (a : Fin 7 → ℝ)
    (ha : StrictMono a) (hsign : ∀ i : Fin 6, T (a i.castSucc)*T (a i.succ) < 0) :
    ∃ r : Fin 6 → ℝ, StrictMono r ∧
      ∀ i, a i.castSucc < r i ∧ r i < a i.succ ∧ T (r i) = 0 := by
  have hex (i : Fin 6) : ∃ y ∈ Ioo (a i.castSucc) (a i.succ), T y = 0 := by
    have hab := (ha (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
    rcases mul_neg_iff.mp (hsign i) with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact intermediate_value_Ioo' hab hT.continuousOn ⟨h₂,h₁⟩
    · exact intermediate_value_Ioo hab hT.continuousOn ⟨h₁,h₂⟩
  choose r hr hTr using hex
  refine ⟨r, ?_, fun i => ⟨(hr i).1,(hr i).2,hTr i⟩⟩
  intro i j hij
  have hab : i.succ ≤ j.castSucc := hij
  exact ((hr i).2.trans_le (ha.monotone hab)).trans (hr j).1

/-- Multiplication by the second harmonic converts a real degree-two
trigonometric polynomial to a complex polynomial of degree at most four.
Once expressed that way its signs cannot alternate on all six arcs. -/
theorem no_alternation_of_degree_four (T : ℝ → ℝ) (hT : Continuous T)
    (p : Polynomial ℂ) (hd : p.natDegree ≤ 4)
    (hp : ∀ θ : ℝ, p.eval (circleMap 0 1 θ) = (circleMap 0 1 θ)^2 * (T θ : ℂ))
    (a : Fin 7 → ℝ) (ha : StrictMono a) (hlen : a (Fin.last 6) - a 0 ≤ 2*Real.pi) :
    ¬ (∀ i : Fin 6, T (a i.castSucc)*T (a i.succ) < 0) := by
  classical
  intro hsign
  have h0 : p ≠ 0 := by
    intro hp0
    have hz := hp (a 0)
    rw [hp0, Polynomial.eval_zero] at hz
    have hcircle : circleMap 0 1 (a 0) ≠ 0 := by simp [circleMap, Complex.exp_ne_zero]
    have hT0 : T (a 0) = 0 := by
      exact_mod_cast (mul_eq_zero.mp hz.symm).resolve_left (pow_ne_zero _ hcircle)
    have hn := hsign 0
    change T (a 0) * T (a 1) < 0 at hn
    simp [hT0] at hn
  obtain ⟨r,hr,hx⟩ := six_distinct_zeros T hT a ha hsign
  let z (i : Fin 6) := circleMap 0 1 (r i)
  have hi (i : Fin 6) : r i ∈ Ico (a 0) (a (Fin.last 6)) :=
    ⟨(ha.monotone (Fin.zero_le _)).trans (hx i).1.le,
      (hx i).2.1.trans_le (ha.monotone (Fin.le_last _))⟩
  have hinj : Function.Injective z := by
    intro i j he
    exact hr.injective <| injOn_circleMap_of_abs_sub_le' (by norm_num : (1:ℝ) ≠ 0)
      hlen (hi i) (hi j) he
  let Z := Finset.univ.image z
  have hz : Z.val ⊆ p.roots := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (show w ∈ Finset.univ.image z from hw)
    rw [Polynomial.mem_roots h0]
    change p.eval (circleMap 0 1 (r i)) = 0
    simp [hp, (hx i).2.2]
  have hc : Z.card = 6 := by simp [Z, Finset.card_image_of_injective _ hinj]
  have hdeg := Polynomial.card_le_degree_of_subset_roots hz
  omega

end GaussianChains.Point22
