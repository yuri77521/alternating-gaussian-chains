import BandVerifiedCacheRangeDefs
import CertTreeRanges

/-! Exact four-sample queries on a table with at most two monotonicity changes.
The hypotheses concern successive integers and admit independent chunk checks. -/
namespace GaussianChains.Band.Fast

theorem edgeOK_of_chunk {raw : ℕ → ℤ} {k₁ k₂ first count i : ℕ} {up₁ up₂ up₃ : Bool}
    (h : checkChunk raw k₁ k₂ up₁ up₂ up₃ first count = true)
    (hi : first ≤ i) (hi' : i < first+count) : edgeOK raw k₁ k₂ up₁ up₂ up₃ i = true := by
  have H := List.all_eq_true.mp h (i-first) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hi] using H

/-- Assemble equally sized chunks into all adjacent checks on the full grid.
An empty list of chunks can cover only the zero-edge grid. -/
theorem edges_of_blocks {raw : ℕ → ℤ} {k₁ k₂ blocks width : ℕ} {up₁ up₂ up₃ : Bool}
    (hw : 0 < width)
    (checked : ∀ j < blocks, checkChunk raw k₁ k₂ up₁ up₂ up₃ (j*width) width = true) :
    ∀ i < blocks*width, edgeOK raw k₁ k₂ up₁ up₂ up₃ i = true := by
  intro i hi
  have h := Nat.mod_add_div i width
  rw [Nat.mul_comm width] at h
  have hm := Nat.mod_lt i hw
  exact edgeOK_of_chunk (checked (i/width) ((Nat.div_lt_iff_lt_mul hw).mpr hi))
    (by omega) (by omega)

private def orient (b : Bool) (x : ℤ) := if b then x else -x

private theorem telescope {f : ℕ → ℤ} {a b : ℕ} (hab : a ≤ b)
    (hh : ∀ i, a ≤ i → i < b → f i ≤ f (i+1)) : f a ≤ f b := by
  have h (j : ℕ) : j ≤ b → a ≤ j → f a ≤ f j := by
    induction j with
    | zero =>
      intro _ hj
      have ha : a=0 := by omega
      simp [ha]
    | succ j ih =>
      intro hj ha
      by_cases h : a = j+1
      · simp [h]
      · exact (ih (by omega) (by omega)).trans (hh j (by omega) (by omega))
  exact h b le_rfl hab

private theorem edge_le {raw : ℕ → ℤ} {k₁ k₂ i : ℕ} {up₁ up₂ up₃ : Bool}
    (h : edgeOK raw k₁ k₂ up₁ up₂ up₃ i = true) :
    let d := direction k₁ k₂ up₁ up₂ up₃ i
    orient d (raw i) ≤ orient d (raw (i+1)) := by
  cases e : direction k₁ k₂ up₁ up₂ up₃ i <;> simpa [edgeOK,orient,e] using h

private def IsCandidate (k₁ k₂ l r x : ℕ) :=
  x=l ∨ x=r ∨ x=clamp k₁ l r ∨ x=clamp k₂ l r

private theorem candidate_bound (raw : ℕ → ℤ) {k₁ k₂ l r x : ℕ}
    (h : IsCandidate k₁ k₂ l r x) :
    (range raw k₁ k₂ l r).1 ≤ raw x ∧ raw x ≤ (range raw k₁ k₂ l r).2 := by
  rcases h with rfl | rfl | rfl | rfl <;> simp only [range] <;> omega

/-- Every included node belongs to one of the three monotone subsegments.
The statement permits flat extrema, coincident turns and singleton queries. -/
theorem range_sound {raw : ℕ → ℤ} {k₁ k₂ l p r last : ℕ} {up₁ up₂ up₃ : Bool}
    (hk : k₁ ≤ k₂) (h : ∀ i < last, edgeOK raw k₁ k₂ up₁ up₂ up₃ i = true)
    (hl : l ≤ p) (hr : p ≤ r) (hlast : r ≤ last) :
    (range raw k₁ k₂ l r).1 ≤ raw p ∧ raw p ≤ (range raw k₁ k₂ l r).2 := by
  have part {a b : ℕ} (dir : Bool) (ha : a ≤ p) (hb : p ≤ b) (hend : b ≤ r)
      (ca : IsCandidate k₁ k₂ l r a) (cb : IsCandidate k₁ k₂ l r b)
      (hdir : ∀ i, a ≤ i → i < b → direction k₁ k₂ up₁ up₂ up₃ i = dir) :
      (range raw k₁ k₂ l r).1 ≤ raw p ∧ raw p ≤ (range raw k₁ k₂ l r).2 := by
    have hs (i : ℕ) (hai : a ≤ i) (hib : i < b) :
        orient dir (raw i) ≤ orient dir (raw (i+1)) := by
      simpa only [hdir i hai hib] using edge_le (h i (by omega))
    have h₁ := telescope (f := fun j => orient dir (raw j)) ha
      (fun i hi hi' => hs i hi (by omega))
    have h₂ := telescope (f := fun j => orient dir (raw j)) hb
      (fun i hi hi' => hs i (by omega) hi')
    have hA := candidate_bound raw ca
    have hB := candidate_bound raw cb
    cases dir <;> simp [orient] at h₁ h₂ <;> omega
  by_cases h₁ : p ≤ k₁
  · apply part up₁ (a := l) (b := clamp k₁ l r) hl (by unfold clamp; omega)
      (by unfold clamp; omega) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    intro i _ hi
    unfold clamp at hi
    simp [direction,show i < k₁ by omega]
  by_cases h₂ : p ≤ k₂
  · apply part up₂ (a := clamp k₁ l r) (b := clamp k₂ l r)
      (by unfold clamp; omega) (by unfold clamp; omega) (by unfold clamp; omega)
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
    intro i hi hi'
    unfold clamp at hi hi'
    simp [direction,show ¬i < k₁ by omega,show i < k₂ by omega]
  · apply part up₃ (a := clamp k₂ l r) (b := r) (by unfold clamp; omega) hr le_rfl
      (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
    intro i hi _
    unfold clamp at hi
    simp [direction,show ¬i < k₁ by omega,show ¬i < k₂ by omega]

/-- Both reported extremes are actual node values at indices within the query,
even without the monotonicity hypotheses. -/
theorem range_attained (raw : ℕ → ℤ) (k₁ k₂ l r : ℕ) (hl : l ≤ r) :
    (∃ i, l ≤ i ∧ i ≤ r ∧ raw i = (range raw k₁ k₂ l r).1) ∧
    (∃ i, l ≤ i ∧ i ≤ r ∧ raw i = (range raw k₁ k₂ l r).2) := by
  have pick (v : ℤ) (h : raw l=v ∨ raw r=v ∨ raw (clamp k₁ l r)=v ∨ raw (clamp k₂ l r)=v) :
      ∃ i, l ≤ i ∧ i ≤ r ∧ raw i=v := by
    rcases h with h | h | h | h
    · exact ⟨l,le_rfl,hl,h⟩
    · exact ⟨r,hl,le_rfl,h⟩
    · exact ⟨clamp k₁ l r,by unfold clamp; omega,by unfold clamp; omega,h⟩
    · exact ⟨clamp k₂ l r,by unfold clamp; omega,by unfold clamp; omega,h⟩
  constructor <;> apply pick <;> simp only [range] <;> omega

open GaussianChains.Cert GaussianChains.Cert.Tables

private def Inside (I : Interval) (lo hi : ℚ) := lo ≤ I.lo ∧ I.hi ≤ hi

private theorem inside_hull (A B : Interval) (lo hi : ℚ) :
    Inside (hull A B) lo hi ↔ Inside A lo hi ∧ Inside B lo hi := by
  simp only [Inside,hull,le_min_iff,max_le_iff]
  tauto

private theorem inside_sparse (node : ℕ → Interval) (j base : ℕ) (lo hi : ℚ) :
    Inside (sparse node j base) lo hi ↔ ∀ p, base ≤ p → p < base+2^j → Inside (node p) lo hi := by
  induction j generalizing base with
  | zero =>
    simp only [sparse,pow_zero]
    constructor
    · intro h p h1 h2
      have : p=base := by omega
      simpa [this] using h
    · exact fun h => h base le_rfl (by omega)
  | succ j ih =>
    rw [sparse,inside_hull,ih,ih,pow_succ]
    constructor
    · rintro ⟨a,b⟩ p h1 h2
      by_cases h : p < base+2^j
      · exact a p h1 h
      · exact b p (by omega) (by omega)
    · intro h
      constructor <;> intro p h1 h2 <;> apply h <;> omega

/-- The original sparse table returns exactly the extremal rational endpoints.
The two subqueries may overlap. -/
theorem rangeHull_extrema_iff (node : ℕ → Interval) {l r : ℕ} (hl : l ≤ r) (lo hi : ℚ) :
    (lo ≤ (rangeHull node l r).lo ∧ (rangeHull node l r).hi ≤ hi) ↔
      ∀ p, l ≤ p → p ≤ r → lo ≤ (node p).lo ∧ (node p).hi ≤ hi := by
  let n := r+1-l
  let j := n.log2
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hlen : l+n=r+1 := by dsimp [n]; omega
  have hp : 2^j ≤ n := Nat.log2_self_le hn
  have hp' : n < 2^j*2 := by simpa only [pow_succ] using Nat.lt_log2_self (n := n)
  change Inside (hull (sparse node j l) (sparse node j (r+1-2^j))) lo hi ↔ _
  rw [inside_hull,inside_sparse,inside_sparse]
  constructor
  · rintro ⟨a,b⟩ p h1 h2
    by_cases h : p < l+2^j
    · exact a p h1 h
    · exact b p (by omega) (by omega)
  · intro h
    constructor <;> intro p h1 h2 <;> apply h <;> omega

/-- An enclosure and two in-range witnesses suffice to replace a sparse
query by a more economical exact computation. -/
theorem rangeHull_eq_of_extrema (node : ℕ → Interval) {l r : ℕ} (hl : l ≤ r) (lo hi : ℚ)
    (h : ∀ p, l ≤ p → p ≤ r → lo ≤ (node p).lo ∧ (node p).hi ≤ hi)
    (hlo : ∃ p, l ≤ p ∧ p ≤ r ∧ (node p).lo = lo)
    (hhi : ∃ p, l ≤ p ∧ p ≤ r ∧ (node p).hi = hi) : rangeHull node l r = ⟨lo,hi⟩ := by
  have outer := (rangeHull_extrema_iff node hl lo hi).mpr h
  have inner := (rangeHull_extrema_iff node hl _ _).mp (And.intro le_rfl le_rfl)
  obtain ⟨i, il, ir, ie⟩ := hlo
  obtain ⟨j, jl, jr, je⟩ := hhi
  have lower := (inner i il ir).1
  have upper := (inner j jl jr).2
  have eLo : (rangeHull node l r).lo = lo :=
    le_antisymm (lower.trans_eq ie) outer.1
  have eHi : (rangeHull node l r).hi = hi :=
    le_antisymm outer.2 (je ▸ upper)
  exact congrArg₂ Interval.mk eLo eHi

/-- Equality with the sparse-table query when the lower and upper endpoint
rows are separately decoded from monotone integer branches. Each endpoint
may have its own turning indices, directions, scale and padding. -/
theorem rangeHull_eq_range (node : ℕ → Interval) (low high : ℕ → ℤ)
    (decodeLo decodeHi : ℤ → ℚ) (hmLo : Monotone decodeLo) (hmHi : Monotone decodeHi)
    {a b c d l r last : ℕ} {u v w x y z : Bool}
    (hab : a ≤ b) (hcd : c ≤ d)
    (heLo : ∀ i < last, edgeOK low a b u v w i = true)
    (heHi : ∀ i < last, edgeOK high c d x y z i = true)
    (hn : ∀ p ≤ last, (node p).lo = decodeLo (low p) ∧ (node p).hi = decodeHi (high p))
    (hl : l ≤ r) (hr : r ≤ last) :
    rangeHull node l r =
      ⟨decodeLo (range low a b l r).1, decodeHi (range high c d l r).2⟩ := by
  apply rangeHull_eq_of_extrema node hl
  · intro i li ir
    rw [(hn i (ir.trans hr)).1,(hn i (ir.trans hr)).2]
    exact ⟨hmLo (range_sound hab heLo li ir hr).1,
      hmHi (range_sound hcd heHi li ir hr).2⟩
  · obtain ⟨i,li,ir,h⟩ := (range_attained low a b l r hl).1
    exact ⟨i,li,ir,(hn i (ir.trans hr)).1.trans (congrArg decodeLo h)⟩
  · obtain ⟨i,li,ir,h⟩ := (range_attained high c d l r hl).2
    exact ⟨i,li,ir,(hn i (ir.trans hr)).2.trans (congrArg decodeHi h)⟩

#print axioms rangeHull_eq_range
#print axioms range_sound
#print axioms range_attained
#print axioms rangeHull_eq_of_extrema
end GaussianChains.Band.Fast

