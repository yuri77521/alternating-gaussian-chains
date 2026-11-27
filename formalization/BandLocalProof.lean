import BandContractWitness
import BandVerifiedCacheOracleSound

/-! A local exclusion certificate for one actual support at one scheduled
width and floor band. Child proofs use literal boxes independently of the
path taken to reach them. -/
namespace GaussianChains.Band

open GaussianChains.Cert GaussianChains.Strip

/-- No feasible candidate represented by this box and support can satisfy
all necessary conditions for maximization against this trial. -/
def NodeSafe (s : Slab) (b : Fin s.count) (i : Fin 18) (j : Fin 5) (raw : ChamberBox) : Prop :=
  ∀ {width h : ℝ}, 0 < width → s.width.Mem width → (s.floor b).Mem h →
    0 ≤ h → h < 1/6 → ∀ u : Fin 6 → ℝ, raw.toBox.Mem u → simplex u →
      activeSupport u = support i → (∀ k, u k ≤ u 5) →
      ¬Stationary (support i) j (s.field width) h u

variable {s : Slab} {b : Fin s.count} {i : Fin 18} {j : Fin 5}
variable {raw left right : ChamberBox} {p₁ p₂ : ChamberPass}

/-- One materialized chamber round contains each simplex point with a largest
last coordinate. A tie for largest remains admissible. -/
theorem nodeSafe_of_pass (hc : checkChamberPass raw p₁ = true)
    (safe : NodeSafe s b i j p₁.out) : NodeSafe s b i j raw := by
  intro width h hwidth hw hh h0 h6 u hb hs ha hm
  exact safe hwidth hw hh h0 h6 u (checkChamberPass_sound hc hb hs.2 hm) hs ha hm

theorem nodeSafe_of_chamber (hc : checkChamber raw p₁ p₂ = true)
    (safe : NodeSafe s b i j p₂.out) : NodeSafe s b i j raw := by
  intro width h hwidth hw hh h0 h6 u hb hs ha hm
  exact safe hwidth hw hh h0 h6 u (checkChamber_sound hc hb hs.2 hm) hs ha hm

theorem nodeSafe_void_raw (empty : chamberVoid raw = true) : NodeSafe s b i j raw := by
  intro _ _ _ _ _ _ _ _ hb hs _ _ _
  exact chamberVoid_sound empty hb hs.2

theorem nodeSafe_void_first (hc : checkChamberPass raw p₁ = true)
    (empty : chamberVoid p₁.out = true) : NodeSafe s b i j raw :=
  nodeSafe_of_pass hc (nodeSafe_void_raw empty)

theorem nodeSafe_void (hc : checkChamber raw p₁ p₂ = true)
    (empty : chamberVoid p₂.out = true) : NodeSafe s b i j raw :=
  nodeSafe_of_chamber hc (nodeSafe_void_raw empty)

theorem nodeSafe_test {C : Fast.RawOracle} (V : Fast.Valid s C) (w : Witness)
    (pass : Fast.realTest s C (s.floor b) (support i) j raw.toBox w = true) :
    NodeSafe s b i j raw := by
  intro width h hwidth hw hh h0 h6 u hb hs _ _
  apply Fast.realTest_sound s C V hw _ _ j hh h0 h6.le hb hs w pass
  exact WidthBounds.matched_hasDerivAt (a:=(s.anchor:ℝ)) hwidth 0

theorem nodeSafe_leaf {C : Fast.RawOracle} (V : Fast.Valid s C)
    (hc : checkChamber raw p₁ p₂ = true) (w : Witness)
    (pass : Fast.realTest s C (s.floor b) (support i) j p₂.out.toBox w = true) :
    NodeSafe s b i j raw :=
  nodeSafe_of_chamber hc (nodeSafe_test V w pass)

/-- Each precise closed half of the parent is contained in the corresponding
literal child. A point on the split hyperplane belongs to both halves. -/
theorem nodeSafe_closed_split (axis : Fin 6) (cut : ℤ)
    (hl : Box.subsetB (raw.toBox.Left axis (chamberTick cut)) left.toBox = true)
    (hr : Box.subsetB (raw.toBox.Right axis (chamberTick cut)) right.toBox = true)
    (hL : NodeSafe s b i j left) (hR : NodeSafe s b i j right) : NodeSafe s b i j raw := by
  intro width h hwidth hw hh h0 h6 u hu hs ha hm
  rcases Box.split_cover hu axis (chamberTick cut) with hl' | hr'
  · exact hL hwidth hw hh h0 h6 u (Box.mem_of_subsetB hl hl') hs ha hm
  · exact hR hwidth hw hh h0 h6 u (Box.mem_of_subsetB hr hr') hs ha hm

theorem nodeSafe_split (axis : Fin 6) (cut : ℤ)
    (hc : checkChamber raw p₁ p₂ = true)
    (hl : Box.subsetB (p₂.out.toBox.Left axis (chamberTick cut)) left.toBox = true)
    (hr : Box.subsetB (p₂.out.toBox.Right axis (chamberTick cut)) right.toBox = true)
    (hL : NodeSafe s b i j left) (hR : NodeSafe s b i j right) : NodeSafe s b i j raw :=
  nodeSafe_of_chamber hc (nodeSafe_closed_split axis cut hl hr hL hR)

/-- A true ground state satisfies the transfer conditions on exactly its own
active support. This turns the root exclusion into the physical conclusion
used by the global strip theorem. -/
theorem rowExcluded_of_nodeSafe
    (root : Box.subsetB (initial (support i)) raw.toBox = true)
    (safe : NodeSafe s b i j raw) : RowExcluded s b i := by
  intro width h hwidth hw hh h0 h6 x hx hm ha
  let u := slack h (gap positiveSix x)
  have hs : simplex u := slack_simplex h6 ⟨hx.1, sum_gap _ _⟩
  have largest (k : Fin 6) : u k ≤ u 5 :=
    div_le_div_of_nonneg_right (sub_le_sub_right (hm k) h) (by linarith)
  have hA : activeSupport u = support i := ha
  have hinit : (initial (support i)).Mem u := hA ▸ initial_mem hs largest
  apply safe hwidth hw hh h0 h6 u (Box.mem_of_subsetB root hinit) hs hA largest
  rw [← hA]
  have han : 0 < (s.anchor:ℝ) := by cases s <;> norm_num [Slab.anchor]
  apply groundState_stationary hwidth h6 (WidthBounds.coefficient_pos han hwidth)
    (c := WidthBounds.offset s.anchor width) _ _ _ x hx hm j
  · intro d
    exact (WidthBounds.matched_affine _ _ d).trans (add_comm _ _)
  · exact WidthBounds.matched_deriv_mul hwidth 0
  · exact WidthBounds.matched_deriv_mul hwidth 1

#print axioms nodeSafe_leaf
#print axioms nodeSafe_split
#print axioms rowExcluded_of_nodeSafe

end GaussianChains.Band
