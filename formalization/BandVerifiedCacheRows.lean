import BandVerifiedCacheSeeds

/-! For widths 8, 33/4 and 35/4 all Gaussian derivative factors have common
denominator 4M². Multiplying these integer numerators by the sample ticks and
rounding once after the seven-image sum reproduces the strip grid exactly. -/
namespace GaussianChains.Band.Fixed
open GaussianChains.Cert GaussianChains.Cert.Nodes GaussianChains.Cert.Tables
open GaussianChains.ImageBounds

private abbrev coeffScale : ℕ+ := 268435456
private abbrev denominator : ℕ+ := coeffScale*work

private def weight (anchor : Fin 3) (j : Order) (m : ℤ) : ℤ := match j with
  | .value => 268435456
  | .first => -(2*widthCode anchor*m)*8192
  | .second => (widthCode anchor*m)^2 - 2*widthCode anchor*8192^2

private def pos (p : ℕ) (k : ℤ) : ℤ := (p:ℤ)+k*8192

private def term (anchor : Fin 3) (sample : ℕ → Ticks) (j : Order) (p : ℕ) (k : ℤ) : Ticks :=
  let m := pos p k
  let w := weight anchor j m
  let v := sample m.natAbs
  let a := w*v.lo
  let b := w*v.hi
  ⟨min a b, max a b⟩

private def total (anchor : Fin 3) (sample : ℕ → Ticks) (j : Order) (p : ℕ) : Ticks :=
  ⟨∑ k ∈ Finset.Icc (-3:ℤ) 3, (term anchor sample j p k).lo,
   ∑ k ∈ Finset.Icc (-3:ℤ) 3, (term anchor sample j p k).hi⟩

private def roundRow (v : Ticks) : Ticks :=
  ⟨v.lo*(unit:ℕ)/(denominator:ℕ)-1, -(-v.hi*(unit:ℕ)/(denominator:ℕ))+1⟩

def row (anchor : Fin 3) (sample : ℕ → Ticks) (j : Order) (p : ℕ) : Ticks :=
  roundRow (total anchor sample j p)

private theorem term_eq (anchor : Fin 3) (sample : ℕ → Ticks) (j : Order) (p : ℕ) (k : ℤ) :
    (term anchor sample j p k).decode denominator =
      weightedImage (fun i => (sample i).decode work) grid (s anchor) j p k := by
  let w := weight anchor j (pos p k)
  let v := sample (pos p k).natAbs
  have hterm : term anchor sample j p k =
      Point22.Atlas.Tables.Ticks.rawMul ⟨w,w⟩ v := by
    simp [term, Point22.Atlas.Tables.Ticks.rawMul, w, v]
  rw [hterm, Point22.Atlas.Tables.Ticks.decode_rawMul]
  unfold weightedImage
  congr 1
  change (⟨weight anchor j (pos p k),weight anchor j (pos p k)⟩ : Ticks).decode coeffScale = _
  cases j
  all_goals first
    | change _ = Interval.singleton 1
    | change _ = Interval.singleton (-2 * s anchor * ((p:ℚ)/grid + k))
    | change _ = Interval.singleton ((2 * s anchor * ((p:ℚ)/grid + k))^2 - 2*s anchor)
  all_goals
    simp only [Point22.Atlas.Tables.Ticks.decode, pos, weight, s, grid, coeffScale,
      Interval.singleton] <;> congr 1 <;> push_cast <;> ring

private theorem floor_quot (z : ℤ) :
    ⌊(z:ℚ)/(denominator:ℚ)⌋ = z/(denominator:ℕ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast]

private theorem ceil_quot (z : ℤ) :
    ⌈(z:ℚ)/(denominator:ℚ)⌉ = -(-z/(denominator:ℕ)) := by
  rw [← neg_neg ((z:ℚ)/(denominator:ℚ)), Int.ceil_neg, ← neg_div, ← Int.cast_neg, floor_quot]

private theorem roundRow_eq (v : Ticks) :
    (roundRow v).decode unit =
      let r := (v.decode denominator).roundOut unit
      ⟨r.lo-1/(unit:ℚ), r.hi+1/(unit:ℚ)⟩ := by
  have ha (t : ℤ) : (t:ℚ)/(denominator:ℚ)*(unit:ℚ) = ((t*(unit:ℕ):ℤ):ℚ)/denominator := by
    push_cast
    ring
  simp only [Point22.Atlas.Tables.Ticks.decode, roundRow, Interval.roundOut, ha, floor_quot, ceil_quot]
  congr 1 <;> push_cast <;> ring

theorem row_eq_assemble (anchor : Fin 3) (sample : ℕ → Ticks) (j : Order) (p : ℕ) :
    (row anchor sample j p).decode unit = assemble unit
      (weightedImage (fun i => (sample i).decode work) grid (s anchor) j p) := by
  let J := Finset.Icc (-3:ℤ) 3
  have hl (k : ℤ) := congrArg Interval.lo (term_eq anchor sample j p k)
  have hh (k : ℤ) := congrArg Interval.hi (term_eq anchor sample j p k)
  rw [row, roundRow_eq]
  have he : (total anchor sample j p).decode denominator =
      (⟨∑ k ∈ J, (weightedImage (fun i => (sample i).decode work) grid (s anchor) j p k).lo,
        ∑ k ∈ J, (weightedImage (fun i => (sample i).decode work) grid (s anchor) j p k).hi⟩ : Interval) := by
    unfold Point22.Atlas.Tables.Ticks.decode total J
    push_cast
    rw [Finset.sum_div, Finset.sum_div]
    apply congrArg₂ Interval.mk
    · apply Finset.sum_congr rfl
      intro k _
      simpa only [Point22.Atlas.Tables.Ticks.decode, PNat.mul_coe, Nat.cast_mul] using hl k
    · apply Finset.sum_congr rfl
      intro k _
      simpa only [Point22.Atlas.Tables.Ticks.decode, PNat.mul_coe, Nat.cast_mul] using hh k
  rw [he] <;> rfl

theorem row_eq_gridNode (anchor : Fin 3) {sample : ℕ → Ticks}
    (hs : ∀ n ≤ 32768, (sample n).decode work = (gaussianEntry work (param anchor) n).sample)
    (j : Order) {p : ℕ} (hp : p ≤ 8192) :
    (row anchor sample j p).decode unit = gridNode work unit grid (s anchor) j p := by
  rw [row_eq_assemble]
  apply assemble_congr
  intro k hk
  unfold imageNode weightedImage
  have h : ((p:ℤ)+k*((grid:ℕ):ℤ)).natAbs ≤ 32768 := by
    obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hk
    change ((p:ℤ)+k*8192).natAbs ≤ 32768
    omega
  dsimp only
  rw [hs _ h]
  cases j <;> rfl

/-- Without any supplied sample table, iterating the integer seed from zero
already gives exactly the direct rational grid at every mesh point. -/
theorem row_iterates_eq_gridNode (anchor : Fin 3) (j : Order) {p : ℕ} (hp : p ≤ 8192) :
    (row anchor (fun n => ((step anchor)^[n] (init anchor)).sample) j p).decode unit =
      gridNode work unit grid (s anchor) j p :=
  row_eq_gridNode anchor (fun n _ => congrArg Entry.sample (iterate_eq anchor n)) j hp

#print axioms row_eq_gridNode
#print axioms row_iterates_eq_gridNode
end GaussianChains.Band.Fixed