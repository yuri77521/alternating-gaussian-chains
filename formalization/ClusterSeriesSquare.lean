import ClusterSeriesBlock

namespace GaussianChains.ClusterSeries

/- Squaring a uniformly bounded amplitude with a uniform cubic remainder
in t = w² preserves a cubic remainder even for high Fourier frequencies. -/
private theorem square_remainder {M K : ℝ} (hM : 0 ≤ M) (a b c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f t : ℝ), 0 ≤ t → |f| ≤ M →
      |f - (a + b*t + c*t^2)| ≤ K*t^3 →
      |f^2 - (a^2 + (2*a*b)*t + (b^2 + 2*a*c)*t^2)| ≤ C*t^3 := by
  let small := (M + |a| + |b| + |c|)*K + |2*b*c| + c^2
  let large := M^2 + a^2 + |2*a*b| + |b^2 + 2*a*c|
  refine ⟨max small large, le_trans (by dsimp [large]; positivity) (le_max_right ..), ?_⟩
  intro f t ht hf herr
  have abs_poly (x y z : ℝ) :
      |x + y*t + z*t^2| ≤ |x| + |y| *t + |z| *t^2 := by
    calc
      _ ≤ (|x| + |y*t|) + |z*t^2| := (abs_add_le ..).trans
        (add_le_add (abs_add_le ..) le_rfl)
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg (sq_nonneg t)]
  by_cases h : t ≤ 1
  · let p := a + b*t + c*t^2
    have ht2 : t^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 1+t by linarith)]
    have hp : |p| ≤ |a| + |b| + |c| := (abs_poly a b c).trans <| by
      nlinarith [mul_nonneg (abs_nonneg b) (sub_nonneg.mpr h),
        mul_nonneg (abs_nonneg c) (sub_nonneg.mpr ht2)]
    have hf' : |f+p| ≤ M + |a| + |b| + |c| := by
      linarith [abs_add_le f p]
    have hc' : |2*b*c + c^2*t| ≤ |2*b*c| + c^2 := by
      refine (abs_add_le ..).trans ?_
      rw [abs_mul (c^2) t, abs_of_nonneg (sq_nonneg c), abs_of_nonneg ht]
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    have expand : f^2 - (a^2+(2*a*b)*t+(b^2+2*a*c)*t^2) =
        (f + p)*(f - p) + (2*b*c+c^2*t)*t^3 := by dsimp [p]; ring
    rw [expand]
    calc
      _ ≤ |(f+p)*(f-p)| + |(2*b*c+c^2*t)*t^3| := abs_add_le ..
      _ = |f+p| * |f-p| + |2*b*c+c^2*t| * t^3 := by
        rw [abs_mul (f+p), abs_mul (2*b*c+c^2*t), abs_of_nonneg (pow_nonneg ht 3)]
      _ ≤ (M + |a| + |b| + |c|)*(K*t^3) + (|2*b*c| +c^2)*t^3 :=
        add_le_add (mul_le_mul hf' herr (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right hc' (pow_nonneg ht 3))
      _ = small*t^3 := by dsimp [small]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg ht 3)
  · have h1 : 1 ≤ t := le_of_not_ge h
    have h13 : 1 ≤ t^3 := one_le_pow₀ h1
    have ht3 : t ≤ t^3 := by simpa using (pow_le_pow_right₀ h1 (by decide : 1 ≤ 3))
    have h23 : t^2 ≤ t^3 := pow_le_pow_right₀ h1 (by decide)
    have hf2 : f^2 ≤ M^2 := by
      rw [← sq_abs f]
      exact pow_le_pow_left₀ (abs_nonneg f) hf _
    calc
      _ ≤ |f^2| + |a^2+(2*a*b)*t+(b^2+2*a*c)*t^2| := abs_sub _ _
      _ ≤ |f^2| + (|a^2| + |2*a*b| *t + |b^2+2*a*c| *t^2) :=
        add_le_add le_rfl (abs_poly (a^2) (2*a*b) (b^2+2*a*c))
      _ = f^2 + (a^2 + |2*a*b| *t + |b^2+2*a*c| *t^2) := by
        rw [abs_of_nonneg (sq_nonneg f), abs_of_nonneg (sq_nonneg a)]
      _ ≤ M^2*t^3 + (a^2*t^3 + |2*a*b| *t^3 + |b^2+2*a*c| *t^3) := by
        exact add_le_add (hf2.trans (le_mul_of_one_le_right (sq_nonneg M) h13))
          (add_le_add (add_le_add (le_mul_of_one_le_right (sq_nonneg a) h13)
            (mul_le_mul_of_nonneg_left ht3 (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left h23 (abs_nonneg _)))
      _ = large*t^3 := by dsimp [large]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg ht 3)

/-- Squared-amplitude Taylor polynomial. The phase is -1 at odd
frequencies and +1 at even frequencies. -/
noncomputable def modeQuartic (k l : ℕ) (e w : ℝ) : ℝ :=
  let A := coeff k
  let B := coeff l
  (1-e)^2 - (1-e)*(A-e*B)*w^2 +
    ((A-e*B)^2/4 + (1-e)*(A*(A-1)-e*B*(B-1))/12)*w^4

private theorem fixed_phase_remainder (k l : ℕ) (e : ℝ) (he : |e| = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ,
      |(block k w - e*block l w)^2 - modeQuartic k l e w| ≤ C*w^6 := by
  obtain ⟨K, _, H⟩ := block_fourth_bound k
  obtain ⟨J, _, I⟩ := block_fourth_bound l
  let a := 1-e
  let b := -(coeff k - e*coeff l)/2
  let c := (coeff k*(coeff k-1) - e*coeff l*(coeff l-1))/24
  let M := (2*(k:ℝ)+1) + (2*(l:ℝ)+1)
  obtain ⟨C, hC, hc⟩ := square_remainder (M := M) (K := K+J) (by dsimp [M]; positivity)
    a b c
  refine ⟨C,hC,fun w ↦ ?_⟩
  let f := block k w - e*block l w
  have hf : |f| ≤ M := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, he, one_mul]
    exact add_le_add (block_abs_le k w) (block_abs_le l w)
  have hpoly : f - (a+b*w^2+c*(w^2)^2) =
      (block k w - blockPoly k w) - e*(block l w - blockPoly l w) := by
    dsimp [f, a, b, c, blockPoly]; ring
  have herr : |f - (a+b*w^2+c*(w^2)^2)| ≤ (K+J)*(w^2)^3 := by
    rw [hpoly]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, he, one_mul]
    calc
      _ ≤ K*w^6+J*w^6 := add_le_add (H _) (I _)
      _ = _ := by ring
  have hquartic : a^2+(2*a*b)*w^2+(b^2+2*a*c)*(w^2)^2 = modeQuartic k l e w := by
    dsimp [a,b,c,modeQuartic]; ring
  have hs := hc f (w^2) (sq_nonneg w) hf herr
  rwa [hquartic, ← pow_mul] at hs

/-- One constant works simultaneously for the two frequency parities and every
angular argument, so that no truncation of the Fourier sum is needed. -/
theorem block_square_fourth_bound (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ℝ), (e = -1 ∨ e = 1) → ∀ w : ℝ,
      |(block k w - e*block l w)^2 - modeQuartic k l e w| ≤ C*w^6 := by
  obtain ⟨A, hA, ha⟩ := fixed_phase_remainder k l (-1) (by norm_num)
  obtain ⟨B, _, hb⟩ := fixed_phase_remainder k l 1 (by norm_num)
  refine ⟨max A B, hA.trans (le_max_left ..), fun e he w ↦ ?_⟩
  rcases he with rfl | rfl
  · exact (ha w).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  · exact (hb w).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))

/-- Odd frequencies carry both the constant mass and the quadratic correction. -/
theorem modeQuartic_odd (k l : ℕ) (w : ℝ) :
    modeQuartic k l (-1) w =
      4 - 2*(coeff k+coeff l)*w^2 +
        ((coeff k+coeff l)^2/4 +
          (coeff k*(coeff k-1)+coeff l*(coeff l-1))/6)*w^4 := by
  dsimp [modeQuartic]; ring

/-- The even-frequency contribution survives whenever the block sizes differ. -/
theorem modeQuartic_even (k l : ℕ) (w : ℝ) :
    modeQuartic k l 1 w = (coeff k-coeff l)^2/4*w^4 := by
  dsimp [modeQuartic]; ring

end GaussianChains.ClusterSeries
