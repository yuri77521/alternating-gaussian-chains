import StripBlockProfileGeometry
import StripBlockProfileCoeffs
import StripFreeze

/-! Identification of the frozen Fourier score of a physically movable
block with its normalized scalar profile, including its phase. -/

noncomputable section
namespace GaussianChains.Strip
open Real ClusterSeries Filter Topology
open scoped ComplexConjugate

private theorem profile_summable {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (B ψ : ℕ → ℝ)
    (hb : ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ)) (t : ℝ) :
    Summable (fun k : ℕ => profileTerm 0 (k+1) q B ψ t) := by
  exact (summable_nat_add_iff (f := fun k : ℕ => profileTerm 0 (k+1) q B ψ t) 2).mp
    (profile_tail_summable 0 hq hq1 B ψ hb t)

private theorem tsum_profile {q : ℝ} {B ψ : ℕ → ℝ} {t : ℝ}
    (hs : Summable (fun k : ℕ => profileTerm 0 (k+1) q B ψ t)) :
    (∑' k : ℕ, profileTerm 0 (k+1) q B ψ t) = profile 0 q B ψ t := by
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  exact (add_assoc (profileTerm 0 1 q B ψ t) (profileTerm 0 2 q B ψ t)
    (∑' k : ℕ, profileTerm 0 (k+3) q B ψ t)).symm

theorem blockModeSum_eq_wave {x : Fin 6 → ℝ} {h : ℝ} (hh : h < 1/6)
    (hx : Feasible positiveSix h x) (hlast : largestLast x) (k : Fin 6)
    (hk : k.val < (blocks (labelledSupport h x)).length) (b : Fin 4)
    (hlen : blockLength (labelledSupport h x) k = b.val+1) (n : ℕ) :
    let A := labelledSupport h x
    let a := blockStart A k
    let z := blockCenter x a b h
    blockModeSum x A k n = (blockMultiplier b ((n:ℝ)*(2*π*h)):ℂ) *
      phase ((n:ℝ)*z - blockPeak a b) := by
  dsimp only
  rw [blockModeSum_centered hh hx hlast k hk b hlen n,centeredModeSum_eq,
    sub_eq_add_neg,phase_add_angles,← blockPeak_phase]
  ring

/-- The change of each Fourier mode of the frozen score, with the factors
q and first block multiplier restored. Therefore summing compares physical
energies using the same normalization as the peak tests. -/
theorem frozen_block_increment {x : Fin 6 → ℝ} {s h : ℝ} (hh : h < 1/6)
    (hx : Feasible positiveSix h x) (hlast : largestLast x) (k : Fin 6)
    (hk : k.val < (blocks (labelledSupport h x)).length) (b : Fin 4)
    (hlen : blockLength (labelledSupport h x) k = b.val+1)
    (hM : 0 < blockMultiplier b (2*π*h)) (j : ℕ) (u : ℝ) :
    let A := labelledSupport h x
    let a := blockStart A k
    let z := blockCenter x a b h
    let η := 2*π*h
    let q := exp (-(π^2)/s)
    let B := blockProfileB x b η
    let ψ := blockProfilePhase x a b
    frozenTerm s x (shiftBlock x A k (u/(2*π))) j - frozenTerm s x x j =
      (q*blockMultiplier b η) *
      (profileTerm 0 (j+1) q B ψ (z+u) - profileTerm 0 (j+1) q B ψ z) := by
  let A := labelledSupport h x
  let a := blockStart A k
  let z := blockCenter x a b h
  let η := 2*π*h
  let q := exp (-(π^2)/s)
  let n := j+1
  let P := structureFactor x n
  let M := blockMultiplier b ((n:ℝ)*η)
  let δ := blockPeak a b
  let y := shiftBlock x A k (u/(2*π))
  have hdelta : structureFactor y n - P = (M:ℂ) *
      (phase ((n:ℝ)*(z+u)-δ) - phase ((n:ℝ)*z-δ)) := by
    rw [show structureFactor y n - P = _ from block_structure_delta x A k hk n u,
      blockModeSum_eq_wave hh hx hlast k hk b hlen n]
    change (phase ((n:ℝ)*u)-1)*((M:ℂ)*phase ((n:ℝ)*z-δ)) = _
    rw [show (n:ℝ)*(z+u)-δ = (n:ℝ)*u+((n:ℝ)*z-δ) by ring,phase_add_angles]
    ring
  have hr : (conj P * (structureFactor y n - P)).re =
      M*‖P‖ * cos ((n:ℝ)*(z+u)-δ-P.arg) - M*‖P‖ * cos ((n:ℝ)*z-δ-P.arg) := by
    rw [hdelta,mul_sub,mul_sub,Complex.sub_re,frozen_polar_re,frozen_polar_re]
  have hpow : q^(n^2) = q*q^(n^2-1) := by
    rw [← pow_succ',Nat.sub_add_cancel (show 0 < n^2 by dsimp [n]; positivity)]
  dsimp only
  change q^(n^2)*(conj P*structureFactor y n).re-q^(n^2)*(conj P*P).re = _
  rw [←mul_sub,←Complex.sub_re,←mul_sub,hr,hpow]
  change _ = q*blockMultiplier b η *
    (profileTerm 0 n q (blockProfileB x b η) (blockProfilePhase x a b) (z+u) -
     profileTerm 0 n q (blockProfileB x b η) (blockProfilePhase x a b) z)
  simp only [profileTerm,Nat.cast_zero,pow_zero,one_mul,zero_mul,add_zero,blockProfileB,
    blockProfilePhase]
  change _ = q*blockMultiplier b η *
    (q^(n^2-1)*(‖P‖*M/blockMultiplier b η)*cos ((n:ℝ)*(z+u)+(-δ-P.arg)) -
     q^(n^2-1)*(‖P‖*M/blockMultiplier b η)*cos ((n:ℝ)*z+(-δ-P.arg)))
  rw [show (n:ℝ)*(z+u)+(-δ-P.arg) = (n:ℝ)*(z+u)-δ-P.arg by ring,
      show (n:ℝ)*z+(-δ-P.arg) = (n:ℝ)*z-δ-P.arg by ring]
  field_simp [show blockMultiplier b η ≠ 0 from hM.ne']
  <;> ring

theorem ground_block_profile {s h : ℝ} (hs : 0 < s) (hh0 : 0 < h) (hh : h < 1/6)
    (hη : 2*π*h ≤ π/5) {x : Fin 6 → ℝ} (hx : IsGroundState positiveSix h s x)
    (hlast : largestLast x) (halign : structureFactor x 1 = (‖structureFactor x 1‖:ℂ))
    (k : Fin 6) (hk : k.val < (blocks (labelledSupport h x)).length) (b : Fin 4)
    (hlen : blockLength (labelledSupport h x) k = b.val+1) :
    let a := blockStart (labelledSupport h x) k
    let z := blockCenter x a b h
    let q := exp (-(π^2)/s)
    ∃ B ψ : ℕ → ℝ, IsLocalMax (profile 0 q B ψ) z ∧
      (∀ t, profileTerm 0 1 q B ψ t = ‖structureFactor x 1‖*cos (t-blockPeak a b)) ∧
      |B 2| ≤ 8 ∧ ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ) := by
  let A := labelledSupport h x
  let a := blockStart A k
  let z := blockCenter x a b h
  let η := 2*π*h
  let q := exp (-(π^2)/s)
  let B := blockProfileB x b η
  let ψ := blockProfilePhase x a b
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos pi_pos)) hs)
  have hM := blockMultiplier_pos b (show 0 < η by dsimp [η]; positivity) hη
  have hb := blockProfileB_bounds (fun i => hh0.le.trans (hx.1 i)) b
    (show 0 < η by dsimp [η]; positivity) hη
  refine ⟨B,ψ,?_,blockProfile_first halign a b hM q,hb⟩
  have hmove : Tendsto (fun t : ℝ => (t-z)/(2*π)) (𝓝 z) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => (t-z)/(2*π)) z := by fun_prop
    simpa using hc.tendsto
  filter_upwards [hmove.eventually (shiftBlock_feasible hh hx.1 hlast k)] with t ht
  let y := shiftBlock x A k ((t-z)/(2*π))
  have hf := frozen_at_minimizer 3 (by decide) hs x y (hx.2 _ ht)
  have hle : (∑' j : ℕ, (frozenTerm s x y j - frozenTerm s x x j)) ≤ 0 := by
    rw [(frozen_summable hs x y).tsum_sub (frozen_summable hs x x)]
    exact sub_nonpos.mpr hf
  have mode (j : ℕ) : frozenTerm s x y j-frozenTerm s x x j =
      (q*blockMultiplier b η)*(profileTerm 0 (j+1) q B ψ t - profileTerm 0 (j+1) q B ψ z) := by
    have H := frozen_block_increment (s:=s) hh hx.1 hlast k hk b hlen hM j (t-z)
    change _ = _ * (profileTerm 0 (j+1) q B ψ (z+(t-z)) - _) at H
    rwa [show z+(t-z)=t by ring] at H
  have hsum (v : ℝ) := profile_summable hq.le hq1 B ψ hb.2 v
  rw [tsum_congr mode,tsum_mul_left,(hsum t).tsum_sub (hsum z),
    tsum_profile (hsum t),tsum_profile (hsum z)] at hle
  exact sub_nonpos.mp (le_of_not_gt fun H => (not_lt_of_ge hle) (mul_pos (mul_pos hq hM) H))

#print axioms ground_block_profile
end GaussianChains.Strip
