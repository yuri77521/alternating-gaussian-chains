import ClustersMoments

noncomputable section
open Finset AlternatingMoments

namespace GaussianChains.OddBlock

/-- An increment of gap number `p` (one-based) at fixed signed first moment.
The prefix moves when `p` is even and the suffix moves when `p` is odd. -/
def varyGap (u : ℕ → ℝ) (p : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  u i + (if p ≤ i then t else 0) - (if p % 2 = 0 then t else 0)

theorem varied_gap (u : ℕ → ℝ) (p : ℕ) (t : ℝ) (i : ℕ) :
    varyGap u p t (i+1) - varyGap u p t i =
      u (i+1)-u i + (if i+1 = p then t else 0) := by
  unfold varyGap
  split_ifs <;> first | omega | ring

theorem varied_first_moment (u : ℕ → ℝ) {j p : ℕ}
    (hp : 0 < p) (hpj : p ≤ 2*j) (t : ℝ) :
    altSum (varyGap u p t) j = altSum u j := by
  rw [firstMoment, firstMoment]
  have g (r : ℕ) : gapB (varyGap u p t) r =
      gapB u r + (if 2*r+2=p then t else 0) := varied_gap u p t (2*r+1)
  simp_rw [g]
  rw [sum_add_distrib]
  by_cases he : p % 2 = 0
  · have hd (i : ℕ) : (2*i+2=p) ↔ (i=p/2-1) := by omega
    simp_rw [hd, sum_ite_eq', mem_range]
    simp [varyGap, hp.not_ge, he, show p/2-1 < j by omega]
  · have hd (i : ℕ) : 2*i+2 ≠ p := by omega
    simp [hd, varyGap, hp.not_ge, he]

/-- A feasible decrease changes just one gap and keeps every internal
constraint valid, including when the new value lands exactly on the floor. -/
theorem varied_feasible (u : ℕ → ℝ) {j p : ℕ} {η t : ℝ}
    (hg : ∀ i < 2*j, η ≤ u (i+1)-u i)
    (ht : η ≤ u p - u (p-1) + t) :
    ∀ i < 2*j, η ≤ varyGap u p t (i+1) - varyGap u p t i := by
  intro i hi
  rw [varied_gap]
  split_ifs with h
  · subst p
    simpa using ht
  · simpa using hg i hi

/-- Shrinking the active gap moves the first endpoint weakly to the right
and the last weakly to the left. Adjacent external gaps therefore stay open. -/
theorem varied_endpoints (u : ℕ → ℝ) {j p : ℕ} (hp : 0 < p)
    (hpj : p ≤ 2*j) {t : ℝ} (ht : t ≤ 0) :
    u 0 ≤ varyGap u p t 0 ∧ varyGap u p t (2*j) ≤ u (2*j) := by
  unfold varyGap
  simp only [hp.not_ge, ↓reduceIte, add_zero, hpj]
  split_ifs <;> constructor <;> linarith

/-- Velocity of each site, in angular units per unit change of one internal gap. -/
def gapVelocity (p i : ℕ) : ℝ :=
  (if p ≤ i then 1 else 0) - (if p % 2 = 0 then 1 else 0)

theorem varyGap_affine (u : ℕ → ℝ) (p i : ℕ) (t : ℝ) :
    varyGap u p t i = u i+t*gapVelocity p i := by
  unfold varyGap gapVelocity
  split_ifs <;> ring

theorem gapVelocity_bound (p i j : ℕ) :
    |gapVelocity p i| ≤ 1 ∧ |gapVelocity p i-gapVelocity p j| ≤ 1 := by
  unfold gapVelocity
  split_ifs <;> norm_num

/-- The derivative bound is for the true signed coordinate variance along
the affine site path, for every internal gap of every odd block. -/
theorem variance_path_derivative (u : ℕ → ℝ) {j p : ℕ} (hp : 0 < p)
    (hpj : p ≤ 2*j) {η : ℝ} (hη : 0 ≤ η) (hg : ∀ i < 2*j, η ≤ u (i+1)-u i) :
    ∃ dV : ℝ, 2*η ≤ dV ∧
      HasDerivAt (fun t =>
        altSum (fun i => (varyGap u p t i)^2) j - (altSum (varyGap u p t) j)^2) dV 0 := by
  set a := gapA u
  set b := gapB u
  have ha (i : ℕ) (hi : i < j) : η ≤ a i := hg (2*i) (by omega)
  have hb (i : ℕ) (hi : i < j) : η ≤ b i := hg (2*i+1) (by omega)
  rcases Nat.mod_two_eq_zero_or_one p with he | ho
  · let r := p/2-1
    have hr : r < j := by dsimp [r]; omega
    obtain ⟨_,hd,_,hmin⟩ := gap_derivatives j r hr a b hη ha hb
    refine ⟨_,hmin,?_⟩
    convert hd using 1
    funext t
    rw [secondMoment]
    change gapVariance j (gapA (varyGap u p t)) (gapB (varyGap u p t)) = _
    congr 1
    · funext i
      change varyGap u p t (2*i+1) - varyGap u p t (2*i) = _
      simp only [varied_gap, if_neg (by omega : 2*i+1≠p), add_zero, a, gapA]
    · funext i
      change varyGap u p t ((2*i+1)+1) - varyGap u p t (2*i+1) = _
      simp only [varied_gap, show (2*i+1+1=p) ↔ (i=r) by dsimp [r]; omega, b, gapB]
  · let r := p/2
    have hr : r < j := by dsimp [r]; omega
    obtain ⟨hd,_,hmin,_⟩ := gap_derivatives j r hr a b hη ha hb
    refine ⟨_,hmin,?_⟩
    convert hd using 1
    funext t
    rw [secondMoment]
    change gapVariance j (gapA (varyGap u p t)) (gapB (varyGap u p t)) = _
    congr 1
    · funext i
      change varyGap u p t (2*i+1) - varyGap u p t (2*i) = _
      simp only [varied_gap, show (2*i+1=p) ↔ (i=r) by dsimp [r]; omega, a, gapA]
    · funext i
      change varyGap u p t ((2*i+1)+1) - varyGap u p t (2*i+1) = _
      simp only [varied_gap, if_neg (by omega : 2*i+1+1≠p), add_zero, b, gapB]

end GaussianChains.OddBlock
