import CertTreeSeeds
import CertTreeTails

/-! The seven signed image entries at a spatial mesh node. All data functions
below use rational arithmetic; the proof identifies their bounds with the
corresponding true spatial derivative of the physical periodized kernel. -/

namespace GaussianChains.Cert.Tables

open GaussianChains.ImageBounds Interval Nodes

private def multiplier : Order → ℚ → ℚ → ℚ
  | .value, _, _ => 1
  | .first, s, t => -2*s*t
  | .second, s, t => (2*s*t)^2-2*s

/-- The signed value, first derivative or second derivative of one image. -/
def weightedImage (samples : ℕ → Interval) (M : ℕ+) (s : ℚ) (j : Order) (p : ℕ) (k : ℤ) : Interval :=
  let n : ℤ := (p:ℤ) + k*((M:ℕ):ℤ)
  (singleton (multiplier j s ((p:ℚ)/M+k))).mul (samples n.natAbs)

def imageNode (scale M : ℕ+) (s : ℚ) (j : Order) (p : ℕ) (k : ℤ) : Interval :=
  weightedImage (fun i => (gaussianEntry scale (s/(M:ℚ)^2) i).sample) M s j p k

theorem imageNode_sound (scale M : ℕ+) {s : ℚ} (hs : 0 ≤ s)
    (j : Order) (p : ℕ) (k : ℤ) :
    (imageNode scale M s j p k).Mem (image j (s:ℝ) ((p:ℝ)/M+k)) := by
  let n : ℤ := (p:ℤ) + k*((M:ℕ):ℤ)
  have hM : (M:ℝ) ≠ 0 := by exact_mod_cast M.ne_zero
  have harg : (p:ℝ)/M + k = (n:ℝ)/M := by
    dsimp [n]
    push_cast
    field_simp
  have hsq : (n.natAbs:ℝ)^2 = (n:ℝ)^2 := by
    simpa only [Int.cast_natCast, Int.cast_pow, Nat.cast_pow] using
      congrArg (fun v : ℤ => (v:ℝ)) (Int.natAbs_sq n)
  have hE := gaussianEntry_sound scale (z:=s/(M:ℚ)^2) (div_nonneg hs (sq_nonneg _)) n.natAbs
  have heq : -((s/(M:ℚ)^2:ℚ):ℝ)*(n.natAbs:ℝ)^2 =
      -(s:ℝ)*((p:ℝ)/M+k)^2 := by
    push_cast
    rw [hsq, harg, div_pow]
    ring
  rw [heq] at hE
  have h := mul_mem (singleton_mem (multiplier j s ((p:ℚ)/M+k))) hE
  cases j <;> simpa [imageNode, weightedImage, n, multiplier, image] using h

private def retained : Finset ℤ := Finset.Icc (-3:ℤ) 3

/-- Round the retained seven-image sum outwards to the chosen output unit,
then reserve one further unit on each side for both infinite tails. -/
def assemble (unit : ℕ+) (images : ℤ → Interval) : Interval :=
  let lo := ∑ k ∈ retained, (images k).lo
  let hi := ∑ k ∈ retained, (images k).hi
  let R := (⟨lo,hi⟩ : Interval).roundOut unit
  ⟨R.lo-1/(unit:ℚ), R.hi+1/(unit:ℚ)⟩

def gridNode (scale unit M : ℕ+) (s : ℚ) (j : Order) (p : ℕ) : Interval :=
  assemble unit (imageNode scale M s j p)

theorem assemble_congr (unit : ℕ+) {f g : ℤ → Interval}
    (h : ∀ k ∈ Finset.Icc (-3:ℤ) 3, f k = g k) : assemble unit f = assemble unit g := by
  have hlo : (∑ k ∈ retained, (f k).lo) = ∑ k ∈ retained, (g k).lo :=
    Finset.sum_congr rfl (fun k hk => congrArg Interval.lo (h k hk))
  have hhi : (∑ k ∈ retained, (f k).hi) = ∑ k ∈ retained, (g k).hi :=
    Finset.sum_congr rfl (fun k hk => congrArg Interval.hi (h k hk))
  simp only [assemble,hlo,hhi]

/-- One output unit must dominate the analytic error bound. No mesh-size or
decimal-precision assumption is used by the finite recurrence itself. -/
theorem gridNode_sound (scale unit M : ℕ+) {s : ℚ} {u : ℝ} {a : ℕ} (j : Order)
    {p : ℕ} (hp : p ≤ (M:ℕ)) (ha : 1 ≤ a) (has : (a:ℝ) ≤ (s:ℝ)) (hsu : (s:ℝ) ≤ u)
    (he : 4*(((2*u)^2*25+2*u)*(1/2:ℝ)^(9*a)) ≤ 1/(unit:ℝ)) :
    (gridNode scale unit M s j p).Mem
      ((deriv^[orderIndex j] (GaussianChains.kernel (s:ℝ))) ((p:ℝ)/M)) := by
  have hs : (0:ℝ) ≤ (s:ℝ) := (Nat.cast_nonneg a).trans has
  have hM : 0 < (M:ℝ) := by exact_mod_cast M.2
  have hx : (p:ℝ)/M ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg p) hM.le
    · apply (div_le_iff₀ hM).mpr
      simpa using (show (p:ℝ) ≤ (M:ℝ) by exact_mod_cast hp)
  let entries := imageNode scale M s j p
  let S : Interval := ⟨∑ k ∈ retained, (entries k).lo, ∑ k ∈ retained, (entries k).hi⟩
  have hsum : S.Mem (seven (fun k => image j (s:ℝ) ((p:ℝ)/M+k))) := by
    have h (k : ℤ) := imageNode_sound scale M (by exact_mod_cast hs : 0 ≤ s) j p k
    rw [seven_eq_Icc]
    constructor
    · simpa [S, retained, entries] using Finset.sum_le_sum
        (s:=Finset.Icc (-3:ℤ) 3) (fun k _ => (h k).1)
    · simpa [S, retained, entries] using Finset.sum_le_sum
        (s:=Finset.Icc (-3:ℤ) 3) (fun k _ => (h k).2)
  have hr := roundOut_mem hsum unit
  have hdiff := abs_le.mp (seven_image_error j ha has hsu hx).2
  rw [iteratedDeriv_eq_series ((Nat.cast_pos.mpr (by omega : 0 < a)).trans_le has)]
  change (gridNode scale unit M s j p).Mem (∑' k : ℤ, image j (s:ℝ) ((p:ℝ)/M+k))
  change (((S.roundOut unit).lo - 1/(unit:ℚ) : ℚ) : ℝ) ≤ _ ∧ _ ≤ (((S.roundOut unit).hi + 1/(unit:ℚ) : ℚ) : ℝ)
  constructor
  · push_cast
    linarith [hdiff.1,hr.1]
  · push_cast
    linarith [hdiff.2,hr.2]

theorem gridNode_strip_sound (scale M : ℕ+) {s : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9)
    (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    (gridNode scale 1000000000 M s j p).Mem
      ((deriv^[orderIndex j] (GaussianChains.kernel (s:ℝ))) ((p:ℝ)/M)) :=
  gridNode_sound scale _ M j hp (a:=8) (u:=9) (by decide) (by exact_mod_cast hs.1)
    (by exact_mod_cast hs.2) (by norm_num)

theorem gridNode_point_sound (scale unit M : ℕ+) (hu : (unit:ℕ) ≤ 100000000000)
    (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    (gridNode scale unit M 22 j p).Mem
      ((deriv^[orderIndex j] (GaussianChains.kernel 22)) ((p:ℝ)/M)) := by
  have hU : (unit:ℝ) ≤ 100000000000 := by exact_mod_cast hu
  have hU0 : 0 < (unit:ℝ) := by exact_mod_cast unit.2
  have he : (1:ℝ)/100000000000 ≤ 1/(unit:ℝ) :=
    one_div_le_one_div_of_le hU0 hU
  exact_mod_cast gridNode_sound scale unit M (s:=22) (a:=22) (u:=22) j hp (by decide)
    (by norm_num) (by norm_num) ((by norm_num : (4:ℝ)*(((2*22)^2*25+2*22)*(1/2:ℝ)^(9*(22:ℕ))) ≤
    1/100000000000).trans he)

#print axioms gridNode_sound
#print axioms gridNode_strip_sound
#print axioms gridNode_point_sound

end GaussianChains.Cert.Tables

