import StripMultipliers
import StripProfile
import StripProjection
import ClusterSeriesAmplitude

/-! The normalized amplitudes and phases of an independently translated block.
The mode-one peak keeps track of its starting charge and length parity. -/
noncomputable section
namespace GaussianChains.Strip
open Real ClusterSeries
open scoped ComplexConjugate

def blockQuadrant (a : ℕ) (b : Fin 4) : ℕ :=
  2*(a%2) + if b.val%2=1 then 1 else 0

def blockPeak (a : ℕ) (b : Fin 4) : ℝ := (blockQuadrant a b : ℝ)*(π/2)

def blockProfileB (x : Fin 6 → ℝ) (b : Fin 4) (η : ℝ) (n : ℕ) : ℝ :=
  ‖structureFactor x n‖ * blockMultiplier b ((n:ℝ)*η) / blockMultiplier b η

def blockProfilePhase (x : Fin 6 → ℝ) (a : ℕ) (b : Fin 4) (n : ℕ) : ℝ :=
  -blockPeak a b - (structureFactor x n).arg

theorem blockProfileB_bounds {x : Fin 6 → ℝ} (hx : Feasible (by decide) 0 x)
    (b : Fin 4) {η : ℝ} (hη : 0 < η) (hmax : η ≤ π/5) :
    |blockProfileB x b η 2| ≤ 8 ∧ ∀ n ≥ 3, |blockProfileB x b η n| ≤ 10*(n:ℝ) := by
  have hM := blockMultiplier_pos b hη hmax
  constructor
  · rw [blockProfileB,abs_div,abs_mul,abs_of_pos hM,abs_of_nonneg (norm_nonneg _)]
    push_cast
    apply (div_le_iff₀ hM).2
    have hnorm : ‖structureFactor x 2‖ ≤ 4 := by
      convert structureFactor_le_two_mul hx 2 using 1 <;> norm_num
    have h := mul_le_mul hnorm (blockMultiplier_second b hη hmax) (abs_nonneg _) (by norm_num)
    linarith only [h]
  · intro n hn
    rw [blockProfileB,abs_div,abs_mul,abs_of_pos hM,abs_of_nonneg (norm_nonneg _)]
    apply (div_le_iff₀ hM).2
    have h := mul_le_mul (structureFactor_le_six x n) (blockMultiplier_high b hη hmax hn)
      (abs_nonneg _) (by norm_num)
    linarith only [h]

theorem blockProfile_first {x : Fin 6 → ℝ}
    (halign : structureFactor x 1 = (‖structureFactor x 1‖:ℂ))
    (a : ℕ) (b : Fin 4) {η : ℝ} (hM : 0 < blockMultiplier b η) (q t : ℝ) :
    profileTerm 0 1 q (blockProfileB x b η) (blockProfilePhase x a b) t =
      ‖structureFactor x 1‖ * cos (t-blockPeak a b) := by
  have harg : (structureFactor x 1).arg = 0 := by
    rw [halign, Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
  simp [profileTerm,blockProfileB,blockProfilePhase,harg,hM.ne',sub_eq_add_neg]

theorem frozen_polar_re (P : ℂ) (M θ δ : ℝ) :
    (conj P * ((M:ℂ) * phase (θ-δ))).re = M*‖P‖*cos (θ-δ-P.arg) := by
  have hc : conj (phase P.arg) = phase (-P.arg) := by
    simp only [phase,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
      Complex.ofReal_neg, mul_neg, neg_mul]
  have hcP : conj P = (‖P‖:ℂ) * phase (-P.arg) := by
    have h : (‖P‖:ℂ)*phase P.arg = P := Complex.norm_mul_exp_arg_mul_I P
    simpa only [map_mul,Complex.conj_ofReal,hc] using (congrArg (fun z : ℂ => conj z) h).symm
  have hph : phase (-P.arg) * phase (θ-δ) = phase (θ-δ-P.arg) := by
    simp only [phase,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hcP,show (‖P‖:ℂ)*phase (-P.arg)*((M:ℂ)*phase (θ-δ)) =
    ((M*‖P‖:ℝ):ℂ)*(phase (-P.arg)*phase (θ-δ)) by push_cast; ring,
    hph,Complex.re_ofReal_mul,phase,Complex.exp_ofReal_mul_I_re]

/-- The signed rotation of a centered block does not vary with the mode.
For an even block it includes the extra factor −i. -/
theorem blockPeak_phase (a : ℕ) (b : Fin 4) :
    (-1:ℂ)^a * (if b.val%2=1 then -Complex.I else 1) = phase (-blockPeak a b) := by
  have negπ : phase (-π) = -1 := by
    apply Complex.ext <;> simp only [phase,Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im,cos_neg,sin_neg,cos_pi,sin_pi,neg_zero,
      Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im]
  have negHalf : phase (-(π/2)) = -Complex.I := by
    apply Complex.ext <;> simp only [phase,Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im,cos_neg,sin_neg,cos_pi_div_two,sin_pi_div_two,neg_zero,
      Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im]
  have negThree : phase (-(3*(π/2))) = Complex.I := by
    rw [show -(3*(π/2)) = -π + -(π/2) by ring, show ∀ u v, phase (u+v)=phase u*phase v by
      intro u v; simp [phase,add_mul,Complex.exp_add], negπ,negHalf]
    ring
  rcases Nat.even_or_odd a with he | ho
  · have ha : a%2=0 := Nat.even_iff.mp he
    by_cases hb : b.val%2=1
    · have hp : blockPeak a b = π/2 := by simp [blockPeak,blockQuadrant,ha,hb]
      rw [hp,negHalf,he.neg_one_pow,if_pos hb,one_mul]
    · have hp : blockPeak a b = 0 := by simp [blockPeak,blockQuadrant,ha,hb]
      simp [hp,he.neg_one_pow,hb,phase]
  · have ha : a%2=1 := Nat.odd_iff.mp ho
    by_cases hb : b.val%2=1
    · have hp : blockPeak a b = 3*(π/2) := by norm_num [blockPeak,blockQuadrant,ha,hb]
      rw [hp,negThree,ho.neg_one_pow,if_pos hb]
      ring
    · have hp : blockPeak a b = π := by norm_num [blockPeak,blockQuadrant,ha,hb] <;> ring
      rw [hp,negπ,ho.neg_one_pow,if_neg hb,mul_one]

end GaussianChains.Strip
