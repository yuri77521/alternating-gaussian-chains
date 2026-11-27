import Point22AtlasRangeTicks
import Point22AtlasTablesFixed
import Point22AtlasLookup
import CertTreeInterpolation

/-! Lift the verified integer runs of signed node intervals to entire continuous
block ranges. The endpoint pad uses the second derivative of the queried order. -/
namespace GaussianChains.Point22.Atlas

open GaussianChains.Cert GaussianChains.ImageBounds
open RangeTicks Tables

private theorem ticks_mem {v : Ticks} {t : ℝ} :
    (v.decode unit).Mem t ↔ (v.lo:ℝ) ≤ 10^11*t ∧ 10^11*t ≤ (v.hi:ℝ) := by
  norm_num [Ticks.decode, Interval.Mem, unit]
  constructor <;> rintro ⟨l,r⟩ <;> constructor <;> linarith

private theorem rawBlock_mem {node : Order → ℕ → Ticks}
    (hn : ∀ j p, p < 32000 → ((node j p).decode unit).Mem (mode (orderIndex j) ((p:ℝ)/32000)))
    (a b : ℕ) (ord : Order) (p : ℕ) :
    ((rawBlock node a b ord p).decode unit).Mem (blockValue a b (orderIndex ord) ((p:ℝ)/32000)) := by
  apply ticks_mem.mpr
  let get (i j : ℕ) := signed i j (node ord (slot p i j))
  let atom (i j : ℕ) := (blockSign i j : ℝ)*mode (orderIndex ord) ((p:ℝ)/32000+shift i j)
  have hterm (i j : ℕ) :
      ((get i j).lo:ℝ) ≤ 10^11*atom i j ∧ 10^11*atom i j ≤ ((get i j).hi:ℝ) := by
    have ht := ticks_mem.mp (hn ord _ (residue_lt p i j))
    unfold atom
    rw [mode_residue]
    by_cases h : (i+j)%2 = 0
    · simpa [get,signed,blockSign,neg_one_pow_eq_ite,Nat.even_iff,h,slot,residue,meshIndex] using ht
    · simp only [get,signed,h,if_false,blockSign,neg_one_pow_eq_ite,Nat.even_iff,
        Rat.cast_neg,Rat.cast_one,neg_one_mul,Int.cast_neg]
      change _ ≤ _ ∧ _ ≤ _
      dsimp only [slot,residue,meshIndex] at ht ⊢
      constructor <;> linarith only [ht.1,ht.2]
  change ((∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (get i j).lo : ℤ):ℝ) ≤
      10^11 * (∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, atom i j) ∧ _
  change _ ∧ 10^11 * (∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, atom i j) ≤
      ((∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (get i j).hi : ℤ):ℝ)
  push_cast
  simp only [Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro i hi <;> apply Finset.sum_le_sum <;>
    intro j hj
  · exact (hterm i j).1
  · exact (hterm i j).2

private theorem padTicks_ge (a b : ℕ) (j : Order) :
    (a:ℝ)*b*(orderCap j:ℝ)/(8*32000^2) ≤ (padTicks a b j:ℝ)/10^11 := by
  let K : ℤ := match j with | .value => 44 | .first => 1500 | .second => 22000
  let num := (a:ℤ)*b*K*10^11
  let quot : ℤ := -num / (8*(32000:ℤ)^2)
  have h := Int.ediv_mul_le (-num) (by decide : 8*(32000:ℤ)^2 ≠ 0)
  have h' : (quot:ℝ)*(8*32000^2) ≤ -(num:ℝ) := by exact_mod_cast h
  have e : (K:ℝ) = (orderCap j:ℝ) := by cases j <;> norm_num [K,orderCap]
  have hn : (num:ℝ) = (a:ℝ)*b*(orderCap j:ℝ)*10^11 := by
    dsimp [num]
    push_cast
    rw [e]
    norm_num
  change _ ≤ ((-quot:ℤ):ℝ) / 10^11
  rw [Int.cast_neg]
  rw [hn] at h'
  linarith only [h']

/-- Use a single interval for all nodes of a closed query, via the sharp linear interpolation
error on the particular lattice cell containing x. -/
private theorem from_nodes {f f' f'' : ℝ → ℝ} {a b : ℕ} {lo hi e K x : ℝ}
    (h₁ : ∀ t, HasDerivAt f (f' t) t) (h₂ : ∀ t, HasDerivAt f' (f'' t) t)
    (hK : ∀ t, |f'' t| ≤ K) (he : K/(8*32000^2) ≤ e)
    (hn : ∀ p : ℕ, a ≤ p → p ≤ b → f ((p:ℝ)/32000) ∈ Set.Icc (lo+e) (hi-e))
    (hx : x ∈ Set.Icc ((a:ℝ)/32000) ((b:ℝ)/32000)) : f x ∈ Set.Icc lo hi := by
  have hc := (abs_nonneg (f'' x)).trans (hK x)
  have he₀ : 0 ≤ e := (by positivity : 0 ≤ K/(8*32000^2)).trans he
  by_cases h : x = (b:ℝ)/32000
  · subst x
    have hab : a ≤ b := by exact_mod_cast (by linarith [hx.1] : (a:ℝ) ≤ b)
    obtain ⟨hl,hu⟩ := hn b hab le_rfl
    exact ⟨by linarith,by linarith⟩
  let p := ⌊x*32000⌋₊
  have hpos : 0 ≤ x*32000 := by linarith [hx.1,Nat.cast_nonneg (α:=ℝ) a]
  have hpa : a ≤ p := (Nat.le_floor_iff hpos).mpr (by linarith [hx.1])
  have hpb : p < b := (Nat.floor_lt hpos).mpr (by linarith [hx.2.lt_of_ne h])
  have hpc : x ∈ Set.Icc ((p:ℝ)/32000) (((p+1:ℕ):ℝ)/32000) := by
    have hlow := Nat.floor_le hpos
    have hhigh := Nat.lt_floor_add_one (x*32000)
    change ((p:ℝ)/32000 ≤ x) ∧ _
    unfold p
    push_cast
    exact ⟨by linarith,by linarith⟩
  have hs : (p:ℝ)/32000 < ((p+1:ℕ):ℝ)/32000 := by push_cast; linarith
  obtain ⟨hl,hu⟩ := Certificate.interpolation_enclosure hs hpc hc
    (fun y _ => h₁ y) (fun y _ => h₂ y) (fun y _ => hK y)
    (hn p hpa hpb.le) (hn (p+1) (by omega) hpb)
  push_cast at hl hu
  constructor <;> linarith only [hl,hu,he]

theorem checkedClaim_valid {node : Order → ℕ → Ticks}
    (hn : ∀ j p, p < 32000 → ((node j p).decode unit).Mem (mode (orderIndex j) ((p:ℝ)/32000)))
    {c : RangeClaim} (hc : CheckedClaim node c) : RangeValid c := by
  intro j horder x hx
  have hj : ofIndex c.ord = j := by rw [horder]; cases j <;> rfl
  unfold CheckedClaim at hc
  rw [hj] at hc
  apply from_nodes (lo := ((ofTicks c.lo c.hi).lo:ℝ)) (hi := ((ofTicks c.lo c.hi).hi:ℝ))
    (e := (padTicks c.a c.b j:ℝ)/10^11) (blockValue_hasDerivAt _ _ _)
    (blockValue_hasDerivAt _ _ _) (blockValue_cap _ _ j) (padTicks_ge _ _ j) _ hx
  intro p hl hu
  obtain ⟨hlo,hhi⟩ := hc p hl (by omega)
  obtain ⟨al,au⟩ := ticks_mem.mp (rawBlock_mem hn c.a c.b j p)
  change c.lo + padTicks c.a c.b j ≤ _ at hlo
  change _ ≤ c.hi - padTicks c.a c.b j at hhi
  have hlo' : (c.lo:ℝ)+(padTicks c.a c.b j:ℝ) ≤ (rawBlock node c.a c.b j p).lo := by exact_mod_cast hlo
  have hhi' : ((rawBlock node c.a c.b j p).hi:ℝ) ≤ (c.hi:ℝ)-(padTicks c.a c.b j:ℝ) := by
    exact_mod_cast hhi
  norm_num [ofTicks] at *
  constructor <;> linarith only [al,au,hlo',hhi']

#print axioms checkedClaim_valid
end GaussianChains.Point22.Atlas
