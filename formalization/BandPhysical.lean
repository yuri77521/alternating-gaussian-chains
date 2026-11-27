import BandLeaves
import ChainCompact
import StripCuts
import ChainMinimum

noncomputable section
namespace GaussianChains.Band
open GaussianChains.Strip Finset

theorem sum_gaps_arc {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i j : Fin N)
    (hij : i ≤ j) : ∑ k ∈ Ico i j, gap hN x k = x j - x i := by
  let f (n : ℕ) := liftSite hN x (n+1) - liftSite hN x n
  have mapped : ∑ k ∈ Ico i.val j.val, f k = ∑ k ∈ Ico i j, gap hN x k := by
    rw [← Fin.map_valEmbedding_Ico, sum_map]
    rfl
  rw [← mapped, sum_Ico_eq_sub f hij, sum_range_sub, sum_range_sub,
    liftSite_fin, liftSite_fin]
  ring

theorem distance_eq_site_sub {h : ℝ} {u x : Fin 6 → ℝ}
    (hg : ∀ i, gap (by decide) x i = pack h u i) {p : Pair} (hp : p ∈ pairs) :
    distance h u p = x p.2 - x p.1 := by
  have hij := (mem_filter.mp hp).2
  have h := sum_gaps_arc (by decide) x p.1 p.2 hij.le
  simp_rw [hg] at h
  simpa [pack, distance, arc, sum_add_distrib, ← mul_sum, nsmul_eq_mul, Fin.card_Ico] using h

theorem expr_as_score {s h c t : ℝ} {u x : Fin 6 → ℝ} {F : ℕ → ℝ → ℝ}
    (hg : ∀ i, gap (by decide) x i = pack h u i)
    (hF : ∀ d, F 0 d = c + t*kernel s d) :
    expression .value F h u =
      c*(∑ p ∈ pairs, (coefficient p : ℝ)) + t*pairScore s x := by
  have hscore : pairScore s x =
      ∑ p ∈ pairs, (coefficient p : ℝ)*kernel s (x p.2 - x p.1) := by
    simp [pairScore, coefficient, charge, pairs, sum_filter, ← univ_product_univ, sum_product]
  rw [hscore, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [weight, order, mul_one, distance_eq_site_sub hg hp, hF]
  ring

private theorem free_gap {u : Fin 6 → ℝ} {A : Support} {k : Fin 6}
    (hA : activeSupport u = A) (h5 : 0 < u 5) (hk : free A k = true) : 0 < u k := by
  rcases (of_decide_eq_true hk : k = 5 ∨ ∃ i ∈ A, i.castSucc = k) with rfl | ⟨i,hi,rfl⟩
  · exact h5
  · exact (mem_active_iff u i).1 (hA ▸ hi)

/-- The distinguished maximum is slack even if more than one index attains it. -/
theorem largest_pos {u : Fin 6 → ℝ} (hu : simplex u) (hm : ∀ j, u j ≤ u 5) : 0 < u 5 := by
  by_contra! h
  have hz : ∀ i, u i = 0 := fun i => le_antisymm ((hm i).trans h) (hu.1 i)
  have := hu.2
  simp [hz] at this

private theorem coefficient_real (i j : Fin 6) :
    (coefficient (i,j) : ℝ) = charge i * charge j := by
  simp [coefficient, charge]

private theorem crosses_last (p : Pair) : crosses p 5 = 0 := by
  have hj : ¬(5 : Fin 6) < p.2 := by have := p.2.isLt; omega
  simp [crosses, hj]

/-- The full score variation in the original simplex, on each of the fifteen
unordered label pairs. The two selected cuts may include the wrap gap. -/
private theorem raySum_at_zero (n : ℕ) (D : ℝ → ℝ) (x : Fin 6 → ℝ) (a b : Fin 6) :
    raySum n D x a b 0 = ∑ p ∈ pairs, (coefficient p : ℝ) *
        (((crosses p a - crosses p b : ℤ) : ℝ)^n) * D (x p.2-x p.1) := by
  rw [raySum, pairs, sum_filter, ← univ_product_univ, sum_product]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (if i < j then charge i * charge j else 0) *
      ((speed a b j : ℝ) - (speed a b i : ℝ)) ^ n *
      D (x j-x i+0*((speed a b j : ℝ) - (speed a b i : ℝ))) = _
  by_cases hij : i < j
  · have speedEq : speed a b j - speed a b i = crosses (i,j) a - crosses (i,j) b :=
      cut_pair_speed a b i j hij
    simp only [if_pos hij, zero_mul, add_zero, coefficient_real, ← Int.cast_sub, speedEq]
  · simp [hij]

private theorem gradient_eq_ray {h t : ℝ} {F : ℕ → ℝ → ℝ} {D : ℝ → ℝ}
    {x u : Fin 6 → ℝ} (hg : ∀ i, gap (by decide) x i = pack h u i)
    (hD : ∀ d, F 1 d = t * D d) (k : Fin 5) :
    expression (.gradient k) F h u = t * raySum 1 D x k.castSucc 5 0 := by
  rw [expression, raySum_at_zero, mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [distance_eq_site_sub hg hp]
  simp only [weight, order, hD, crosses_last, sub_zero, pow_one, Rat.cast_mul,
    Rat.cast_intCast]
  ring

private theorem curvature_eq_ray {h t : ℝ} {F : ℕ → ℝ → ℝ} {D : ℝ → ℝ}
    {x u : Fin 6 → ℝ} (hg : ∀ i, gap (by decide) x i = pack h u i)
    (hD : ∀ d, F 2 d = t * D d) (a b : Fin 6) :
    expression (.curvature a b) F h u = t * raySum 2 D x a b 0 := by
  rw [expression, raySum_at_zero, mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [distance_eq_site_sub hg hp]
  simp only [weight, order, hD, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast]
  ring

/-- Every floor-constrained global minimizer satisfies all three mathematical
terminal tests for each physical trial, even if the largest gap is tied. -/
theorem groundState_stationary {s h c t : ℝ} (hs : 0 < s) (hh : h < 1/6) (ht : 0 < t)
    {F : ℕ → ℝ → ℝ} (h0 : ∀ d, F 0 d = c + t * kernel s d)
    (h1 : ∀ d, F 1 d = t * deriv (kernel s) d)
    (h2 : ∀ d, F 2 d = t * deriv (deriv (kernel s)) d)
    (x : Fin 6 → ℝ) (hx : IsGroundState (by decide) h s x)
    (hm : ∀ i, gap (by decide) x i ≤ gap (by decide) x 5) (j : Fin 5) :
    let u := slack h (gap (by decide) x)
    Stationary (activeSupport u) j F h u := by
  let u := slack h (gap (by decide) x)
  change Stationary (activeSupport u) j F h u
  have hg (i : Fin 6) : gap (by decide) x i = pack h u i :=
    (congrFun (pack_slack hh _) i).symm
  have hu : simplex u := slack_simplex hh ⟨hx.1, sum_gap _ _⟩
  have hum (i : Fin 6) : u i ≤ u 5 :=
    div_le_div_of_nonneg_right (sub_le_sub_right (hm i) h) (by linarith)
  have pos5 := largest_pos hu hum
  have freePos {k : Fin 6} (hk : free (activeSupport u) k = true) :
      h < gap (by decide) x k :=
    (slack_positive_iff hh _ _).mp (free_gap rfl pos5 hk)
  have d0 (z : ℝ) : HasDerivAt (kernel s) (deriv (kernel s) z) z := by
    rw [ImageCalculus.kernel_periodized]
    exact (ImageCalculus.periodized_derivative hs 1 z).differentiableAt.hasDerivAt
  have d1 (z : ℝ) : HasDerivAt (deriv (kernel s)) (deriv (deriv (kernel s)) z) z := by
    have eq : deriv (kernel s) = ImageCalculus.periodized s (ImageCalculus.next s 1) := by
      funext y
      rw [ImageCalculus.kernel_periodized]
      exact (ImageCalculus.periodized_derivative hs 1 y).deriv
    rw [eq]
    exact (ImageCalculus.periodized_derivative hs _ z).differentiableAt.hasDerivAt
  refine ⟨?_, ?_, ?_⟩
  · let v := fun i => (trial j i : ℝ)
    let y := sitesOfGaps (pack h v)
    have hv := pack_feasible hh.le (trial_simplex j)
    have hy (i : Fin 6) : gap (by decide) y i = pack h v i :=
      gap_sitesOfGaps (by decide) _ hv.2 i
    have hfy : Feasible (by decide) h y := fun i => (hy i).symm ▸ hv.1 i
    rw [expr_as_score hy h0, expr_as_score hg h0]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((imageEnergy_le_iff_pairScore_ge (by decide) s x y).mp (hx.2 y hfy)) ht.le)
  · intro k hk
    have hk' := (slack_positive_iff hh _ _).mp ((mem_active_iff u k).mp hk)
    have h5 := (slack_positive_iff hh _ _).mp pos5
    have hn : k.castSucc ≠ (5 : Fin 6) := by
      intro eq; have he := congrArg Fin.val eq; change k.val = 5 at he; omega
    rw [gradient_eq_ray hg h1, (score_cut_conditions x hx.1 hx.2 d0 d1 hn hk' h5).1, mul_zero]
  · intro a b ha hb hab
    rw [curvature_eq_ray hg h2]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le
      (score_cut_conditions x hx.1 hx.2 d0 d1 hab (freePos ha) (freePos hb)).2

#print axioms groundState_stationary

end GaussianChains.Band
