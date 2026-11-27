import StripSmallFloors
import StripPeak
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise differentiation and uniform first/second remainder bounds for
a real Fourier profile of a freely translating block. The real amplitudes
can carry signs, and each mode may have an independent phase. -/
noncomputable section
namespace GaussianChains.Strip
open Real

def profileTerm (p n : ℕ) (q : ℝ) (B ψ : ℕ → ℝ) (t : ℝ) : ℝ :=
  (n:ℝ)^p * q^(n^2-1) * B n * cos ((n:ℝ)*t+ψ n+(p:ℝ)*(π/2))

def profile (p : ℕ) (q : ℝ) (B ψ : ℕ → ℝ) (t : ℝ) : ℝ :=
  profileTerm p 1 q B ψ t + profileTerm p 2 q B ψ t + ∑' k, profileTerm p (k+3) q B ψ t

theorem profileTerm_deriv (p n : ℕ) (q : ℝ) (B ψ : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (profileTerm p n q B ψ) (profileTerm (p+1) n q B ψ t) t := by
  have hz := (((hasDerivAt_id t).const_mul (n:ℝ)).add_const (ψ n)).add_const ((p:ℝ)*(π/2))
  have hd := hz.cos.const_mul ((n:ℝ)^p*q^(n^2-1)*B n)
  convert hd using 1
  simp only [profileTerm,Nat.cast_add,Nat.cast_one,id_eq,mul_one,pow_succ (n:ℝ) p]
  rw [show (n:ℝ)*t+ψ n+((p:ℝ)+1)*(π/2)=((n:ℝ)*t+ψ n+(p:ℝ)*(π/2))+π/2 by ring,cos_add_pi_div_two]
  ring

private theorem high_profile_bound (p : ℕ) {q : ℝ} (hq : 0 ≤ q) (B ψ : ℕ → ℝ)
    (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (k : ℕ) (t : ℝ) :
    ‖profileTerm p (k+3) q B ψ t‖ ≤ 10*tailTerm (p+1) q k := by
  let n := k+3
  have hs := hb n (by dsimp [n]; omega)
  have hc := abs_cos_le_one ((n:ℝ)*t+ψ n+p*(π/2))
  have hA : 0 ≤ (n:ℝ)^p * q^(n^2-1) := by positivity
  change |(n:ℝ)^p*q^(n^2-1)*B n*cos _| ≤ 10*((n:ℝ)^(p+1)*q^(n^2-1))
  rw [abs_mul,abs_mul,abs_of_nonneg hA,pow_succ (n:ℝ) p]
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul hs hc (abs_nonneg _) (by positivity)) hA]

private theorem abs_majorant {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (p : ℕ) :
    Summable (fun k => 10*tailTerm p q k) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_widthMoment p hq h1)
  exact hs.mul_left 10

/-- Absolute convergence of the tail at every angular midpoint, for use in
comparisons between the frozen energy and the translated-block profile. -/
theorem profile_tail_summable (p : ℕ) {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1)
    (B ψ : ℕ → ℝ) (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (t : ℝ) :
    Summable (fun k => profileTerm p (k+3) q B ψ t) :=
  Summable.of_norm_bounded (abs_majorant hq h1 (p+1)) (fun k => high_profile_bound p hq B ψ hb k t)

theorem profile_deriv (p : ℕ) {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (B ψ : ℕ → ℝ)
    (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (t : ℝ) :
    HasDerivAt (profile p q B ψ) (profile (p+1) q B ψ t) t := by
  have h0 := profile_tail_summable p hq h1 B ψ hb 0
  have htail := hasDerivAt_tsum (abs_majorant hq h1 (p+1+1))
    (fun k z => profileTerm_deriv p (k+3) q B ψ z)
    (fun k z => high_profile_bound (p+1) hq B ψ hb k z) h0 t
  exact ((profileTerm_deriv p 1 q B ψ t).add (profileTerm_deriv p 2 q B ψ t)).add htail

theorem profile_remainder (p : ℕ) {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (B ψ : ℕ → ℝ)
    (h2 : |B 2| ≤ 8) (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (t : ℝ) :
    |profile p q B ψ t - profileTerm p 1 q B ψ t| ≤
      8*(2:ℝ)^p*q^3+10*highTail (p+1) q := by
  have htail := tsum_of_norm_bounded (abs_majorant hq h1 (p+1)).hasSum
    (fun k => high_profile_bound p hq B ψ hb k t)
  rw [tsum_mul_left] at htail
  have hs2 : |profileTerm p 2 q B ψ t| ≤ 8*(2:ℝ)^p*q^3 := by
    dsimp only [profileTerm]
    norm_num only [Nat.cast_ofNat,Nat.reducePow,Nat.reduceSub]
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^p*q^3)]
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul h2 (abs_cos_le_one (2*t+ψ 2+(p:ℝ)*(π/2))) (abs_nonneg _) (by norm_num))
      (by positivity : 0 ≤ (2:ℝ)^p*q^3)
    linarith only [hh]
  rw [profile,show ∀ a b c:ℝ, a+b+c-a=b+c by intros; ring]
  exact (abs_add_le _ _).trans (add_le_add hs2 htail)

/-- A principal representative for the signed offset from the first-harmonic peak. -/
private theorem principalTurn (v : ℝ) : ∃ k : ℤ, |v-(k:ℝ)*(2*π)| ≤ π := by
  let k := ⌊(v+π)/(2*π)⌋
  refine ⟨k,abs_le.mpr ?_⟩
  have hk := Int.floor_le ((v+π)/(2*π))
  have hk' := Int.lt_floor_add_one ((v+π)/(2*π))
  change (k:ℝ) ≤ _ at hk
  change _ < (k:ℝ)+1 at hk'
  have hp : 0 < 2*π := by positivity
  rw [le_div_iff₀ hp] at hk
  rw [div_lt_iff₀ hp] at hk'
  constructor <;> linarith

theorem profile_peak {q A z peak d : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (B ψ : ℕ → ℝ)
    (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (h2 : |B 2| ≤ 8) (hA : 0 < A)
    (hfirst : ∀ t, profileTerm 0 1 q B ψ t = A*cos (t-peak))
    (hmax : IsLocalMax (profile 0 q B ψ) z)
    (hd : 0 ≤ d) (hdπ : d ≤ π/2)
    (hslope : 16*q^3+10*highTail 2 q < A*sin d)
    (hcurve : 32*q^3+10*highTail 3 q < A*cos d) :
    ∃ k : ℤ, |z-(peak+2*π*(k:ℝ))| < d := by
  have H₁ : profileTerm 1 1 q B ψ = fun t => -A*sin (t-peak) := by
    funext t
    have h := profileTerm_deriv 0 1 q B ψ t
    rw [funext hfirst] at h
    have hp := (((hasDerivAt_id t).sub_const peak).cos).const_mul A
    convert h.unique hp using 1 <;> simp <;> ring
  have H₂ : profileTerm 2 1 q B ψ = fun t => -A*cos (t-peak) := by
    funext t
    have h := profileTerm_deriv 1 1 q B ψ t
    rw [H₁] at h
    have hp := (((hasDerivAt_id t).sub_const peak).sin).const_mul (-A)
    convert h.unique hp using 1 <;> simp
  have D₁ : deriv (profile 0 q B ψ) = profile 1 q B ψ :=
    funext fun t => (profile_deriv 0 hq h1 B ψ hb t).deriv
  have D₂ : deriv (profile 1 q B ψ) = profile 2 q B ψ :=
    funext fun t => (profile_deriv 1 hq h1 B ψ hb t).deriv
  obtain ⟨k,hk⟩ := principalTurn (z-peak)
  let u := (z-peak)-(k:ℝ)*(2*π)
  have g := profile_remainder 1 hq h1 B ψ h2 hb z
  have c := profile_remainder 2 hq h1 B ψ h2 hb z
  rw [H₁] at g
  rw [H₂] at c
  have hg : |deriv (profile 0 q B ψ) z+A*sin u| ≤ 16*q^3+10*highTail 2 q := by
    rw [D₁, show sin u=sin (z-peak) from sin_sub_int_mul_two_pi _ _]
    norm_num [neg_mul,sub_neg_eq_add] at g
    exact g
  have hc : |deriv (deriv (profile 0 q B ψ)) z+A*cos u| ≤ 32*q^3+10*highTail 3 q := by
    rw [D₁,D₂, show cos u=cos (z-peak) from cos_sub_int_mul_two_pi _ _]
    norm_num [neg_mul,sub_neg_eq_add] at c
    exact c
  have hnear := two_derivative_peak hmax (profile_deriv 0 hq h1 B ψ hb z).continuousAt hA
    hd hdπ hk hg hc hslope hcurve
  exact ⟨k, by convert hnear using 2 <;> dsimp [u]; ring⟩

end GaussianChains.Strip
