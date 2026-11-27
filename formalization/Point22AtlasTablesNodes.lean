import Point22AtlasTablesFixed

/-! Seven signed images at the frozen 32000-point grid, all in integer ticks.
The only rounding of a row is after its seven retained images are added. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.Cert GaussianChains.Cert.Nodes
open GaussianChains.Cert.Tables GaussianChains.ImageBounds

def weight (j : Order) (m : ℤ) : ℤ := match j with
  | .value => 32000^2
  | .first => -(44*m)*32000
  | .second => (44*m)^2 - 44*32000^2

def pos (p : ℕ) (k : ℤ) : ℤ := (p:ℤ) + k*32000

def term (sample : ℕ → Ticks) (j : Order) (p : ℕ) (k : ℤ) : Ticks :=
  let m := pos p k
  let w := weight j m
  Ticks.rawMul ⟨w,w⟩ (sample m.natAbs)

abbrev denominator : ℕ+ := (grid*grid)*work

def total (sample : ℕ → Ticks) (j : Order) (p : ℕ) : Ticks :=
  ⟨∑ k ∈ Finset.Icc (-3:ℤ) 3, (term sample j p k).lo,
   ∑ k ∈ Finset.Icc (-3:ℤ) 3, (term sample j p k).hi⟩

def roundRow (v : Ticks) : Ticks :=
  ⟨v.lo*(unit:ℕ)/(denominator:ℕ)-1, -(-v.hi*(unit:ℕ)/(denominator:ℕ))+1⟩

def row (sample : ℕ → Ticks) (j : Order) (p : ℕ) : Ticks := roundRow (total sample j p)

private theorem term_eq (sample : ℕ → Ticks) (j : Order) (p : ℕ) (k : ℤ) :
    (term sample j p k).decode denominator =
      weightedImage (fun i => (sample i).decode work) grid 22 j p k := by
  unfold term
  rw [Ticks.decode_rawMul]
  unfold weightedImage
  congr 1
  change (⟨weight j (pos p k),weight j (pos p k)⟩ : Ticks).decode (grid*grid) = _
  have sing (w : ℤ) : (⟨w,w⟩ : Ticks).decode (grid*grid) =
      Interval.singleton ((w:ℚ)/(grid*grid:ℕ+)) := rfl
  rw [sing]
  congr 1
  cases j with
  | value =>
    change _ = 1
    norm_num [weight,grid]
  | first =>
    change _ = -2*22*((p:ℚ)/32000+k)
    norm_num [weight,pos,grid]
    ring
  | second =>
    change _ = (2*22*((p:ℚ)/32000+k))^2-2*22
    norm_num [weight,pos,grid]
    ring

private theorem floor_quot (z : ℤ) :
    ⌊(z:ℚ)/(denominator:ℚ)⌋ = z/(denominator:ℕ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast]

private theorem ceil_quot (z : ℤ) :
    ⌈(z:ℚ)/(denominator:ℚ)⌉ = -(-z/(denominator:ℕ)) := by
  rw [← neg_neg ((z:ℚ)/(denominator:ℚ)), Int.ceil_neg, ← neg_div, ← Int.cast_neg, floor_quot]

private theorem roundRow_eq (v : Ticks) :
    (roundRow v).decode unit =
      let r := (v.decode denominator).roundOut unit
      ⟨r.lo-1/(unit:ℚ),r.hi+1/(unit:ℚ)⟩ := by
  have ha (t : ℤ) : (t:ℚ)/(denominator:ℚ)*(unit:ℚ) = ((t*(unit:ℕ):ℤ):ℚ)/denominator := by
    push_cast
    ring
  simp only [Ticks.decode, roundRow, Interval.roundOut, ha, floor_quot, ceil_quot]
  congr 1 <;> push_cast <;> ring

theorem row_eq_assemble (sample : ℕ → Ticks) (j : Order) (p : ℕ) :
    (row sample j p).decode unit = assemble unit
      (weightedImage (fun i => (sample i).decode work) grid 22 j p) := by
  let J := Finset.Icc (-3:ℤ) 3
  have hl (k : ℤ) := congrArg Interval.lo (term_eq sample j p k)
  have hh (k : ℤ) := congrArg Interval.hi (term_eq sample j p k)
  rw [row, roundRow_eq]
  have he : (total sample j p).decode denominator =
      (⟨∑ k ∈ J, (weightedImage (fun i => (sample i).decode work) grid 22 j p k).lo,
        ∑ k ∈ J, (weightedImage (fun i => (sample i).decode work) grid 22 j p k).hi⟩ : Interval) := by
    unfold Ticks.decode total J
    push_cast
    rw [Finset.sum_div, Finset.sum_div]
    apply congrArg₂ Interval.mk
    · apply Finset.sum_congr rfl; intro k _
      simpa only [Ticks.decode, PNat.mul_coe, Nat.cast_mul] using hl k
    · apply Finset.sum_congr rfl; intro k _
      simpa only [Ticks.decode, PNat.mul_coe, Nat.cast_mul] using hh k
  rw [he]
  rfl

theorem row_eq_gridNode {sample : ℕ → Ticks}
    (hs : ∀ n ≤ 128000, (sample n).decode work = (gaussianEntry work param n).sample)
    (j : Order) {p : ℕ} (hp : p < 32000) :
    (row sample j p).decode unit = gridNode work unit grid 22 j p := by
  rw [row_eq_assemble]
  apply assemble_congr
  intro k hk
  unfold imageNode weightedImage
  have h : ((p:ℤ)+k*((grid:ℕ):ℤ)).natAbs ≤ 128000 := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hk
    change ((p:ℤ)+k*32000).natAbs ≤ 128000
    have hb : |(p:ℤ)+k*32000| ≤ (128000 : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb
  dsimp only
  rw [hs _ h]
  cases j <;> rfl

theorem row_sound {sample : ℕ → Ticks}
    (hs : ∀ n ≤ 128000, (sample n).decode work = (gaussianEntry work param n).sample)
    (j : Order) {p : ℕ} (hp : p < 32000) :
    ((row sample j p).decode unit).Mem ((deriv^[orderIndex j] (kernel 22)) ((p:ℝ)/32000)) := by
  rw [row_eq_gridNode hs j hp]
  exact gridNode_point_sound work unit grid (by decide) j (by exact hp.le)

end GaussianChains.Point22.Atlas.Tables

