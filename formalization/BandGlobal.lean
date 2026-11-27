import BandSlabOracle
import BandPhysicalSchedule
import PackedFaceGapLink
import PackedFaceEnergyTable
import ClustersRotation

/-! Continuous-domain interpretation of the 2016 scheduled roots
(14 narrow floor intervals and two lots of 49 broad ones, with 18
support classes for each). No certificate acceptance is assumed by definition. -/
noncomputable section
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.Strip
open GaussianChains.PackedFace Set

/-- Every packet at its actual floor and support index passes the checker
using the cache at this slab's prescribed anchor. -/
def RowsAccepted (s : Slab) : Prop :=
  ∀ (b : Fin s.count) (i : Fin 18), checkRow s (buildStripCache s.anchor) b i = true

/-- An actual cyclic shift and translation, in the ordered physical lifts. -/
def RepresentsFace (h : ℝ) (x : Fin 6 → ℝ) (k : Fin 6) (t : ℝ) : Prop :=
  ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + sites h t i

def OnFace (h : ℝ) (x : Fin 6 → ℝ) : Prop :=
  ∃ k t, feasible h t ∧ RepresentsFace h x k t

/-- Physical meaning of excluding a scheduled support. The checker may use
any kernel enclosure strong enough to prove this statement. -/
def RowExcluded (slab : Slab) (b : Fin slab.count) (i : Fin 18) : Prop :=
  ∀ {s h : ℝ}, 0 < s → slab.width.Mem s → (slab.floor b).Mem h →
    0 ≤ h → h < 1/6 → ∀ x, IsGroundState positiveSix h s x → largestLast x →
      labelledSupport h x ≠ support i

/-- An accepted typed tree on the prescribed starting box excludes every
true global minimizer on its support. The trial index is fixed in the tree's
leaf test. This form does not require parsing a serialized certificate. -/
theorem rowExcluded_of_tree (slab : Slab) (b : Fin slab.count) (i : Fin 18)
    (j : Fin 5) (t : Cover Witness) {test : Fin 5 → Box 6 → Witness → Bool}
    (pass : check (test j) (initial (support i)) t = true)
    (leaf : ∀ {s h : ℝ}, 0 < s → slab.width.Mem s → (slab.floor b).Mem h → 0 ≤ h → h < 1/6 →
      ∀ j B w u, test j B w = true → B.Mem u → simplex u → activeSupport u = support i →
      (∀ v, u v ≤ u 5) → ¬Stationary (support i) j (slab.field s) h u) :
    RowExcluded slab b i := by
  intro s h hs hw hb h0 h6 x hx hm ha
  let u := slack h (gap positiveSix x)
  have hu : simplex u := slack_simplex h6 ⟨hx.1, sum_gap _ _⟩
  have hm' (v : Fin 6) : u v ≤ u 5 :=
    div_le_div_of_nonneg_right (sub_le_sub_right (hm v) h) (by linarith)
  have hA : activeSupport u = support i := ha
  have hinit : (initial (support i)).Mem u := hA ▸ initial_mem hu hm'
  let P (v : Fin 6 → ℝ) :=
    simplex v ∧ activeSupport v = support i ∧ (∀ w, v w ≤ v 5) ∧
      Stationary (support i) j (slab.field s) h v
  have noP : ¬P u := check_sound (P:=P)
    (fun B w v chk mem H => leaf hs hw hb h0 h6 j B w v chk mem H.1 H.2.1 H.2.2.1 H.2.2.2)
    t _ pass hinit hu.2 hm'
  apply noP
  refine ⟨hu,hA,hm',?_⟩
  rw [←hA]
  have han : 0 < (slab.anchor : ℝ) := by cases slab <;> norm_num [Slab.anchor]
  apply groundState_stationary hs h6 (WidthBounds.coefficient_pos han hs)
    (c := WidthBounds.offset slab.anchor s) _ _ _ x hx hm j
  · intro d
    exact (WidthBounds.matched_affine _ _ d).trans (add_comm _ _)
  · exact WidthBounds.matched_deriv_mul hs 0
  · exact WidthBounds.matched_deriv_mul hs 1

/-- A packet with the registered cut support may use a different sound
leaf test, for example a sharper kernel oracle. -/
theorem rowExcluded_of_packet (slab : Slab) (b : Fin slab.count) (i : Fin 18)
    {test : Fin 5 → Box 6 → Witness → Bool} (pass : packetCheck slab b i test = true)
    (leaf : ∀ {s h : ℝ}, 0 < s → slab.width.Mem s → (slab.floor b).Mem h → 0 ≤ h → h < 1/6 →
      ∀ j B w u, test j B w = true → B.Mem u → simplex u → activeSupport u = support i →
      (∀ v, u v ≤ u 5) → ¬Stationary (support i) j (slab.field s) h u) :
    RowExcluded slab b i := by
  obtain ⟨j,data,hpass⟩ := packetCheck_witness pass
  unfold checkPacket at hpass
  split at hpass
  · exact rowExcluded_of_tree slab b i j _ (test:=test) hpass leaf
  · contradiction

theorem rowExcluded_of_checkRow (slab : Slab) (b : Fin slab.count) (i : Fin 18)
    (hc : checkRow slab (buildStripCache slab.anchor) b i = true) : RowExcluded slab b i := by
  apply rowExcluded_of_packet slab b i hc
  intro s h hs hw hb h0 h6 j B w u pass mem hu _ _
  exact realTest_sound slab hw (WidthBounds.matched_hasDerivAt (a:=(slab.anchor:ℝ)) hs 0) _ j hb h0 h6.le mem hu w pass

/-- Any proof eliminating these eighteen physical support classes at each
scheduled floor implies the identical full-domain statement. -/
theorem packed_of_leaf_checker (slab : Slab) (excluded : ∀ b i, RowExcluded slab b i)
    {s h : ℝ} (hs : 0 < s) (hw : slab.width.Mem s) (h0 : 0 ≤ h)
    (hlo : (slab.edge 0 : ℝ) ≤ h) (h6 : h < 1/6)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) : OnFace h x := by
  obtain ⟨b,hb⟩ := slab.floor_cover hlo h6.le
  apply full_domain_from_support_exclusion h6 _ x hx
  intro y hy hm hA
  obtain ⟨i,hi⟩ := support_covers hA
  exact excluded b i hs hw hb h0 h6 y hy hm hi.symm

/-- From the actual indexed certificates on one width slab to the complete
six-particle feasible domain at any of its covered floors. -/
theorem packed_of_accepted_rows (slab : Slab) (rows : RowsAccepted slab)
    {s h : ℝ} (hs : 0 < s) (hw : slab.width.Mem s) (h0 : 0 ≤ h)
    (hlo : (slab.edge 0 : ℝ) ≤ h) (h6 : h < 1/6)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) : OnFace h x := by
  exact packed_of_leaf_checker slab (fun b i => rowExcluded_of_checkRow slab b i (rows b i))
    hs hw h0 hlo h6 x hx

/-- At h=1/6 the simplex consists of the uniform gap vector. The shift
is left explicit to use the same representation at all closed endpoints. -/
theorem uniform_endpoint_onFace {s : ℝ} (x : Fin 6 → ℝ)
    (hx : IsGroundState positiveSix (1/6) s x) : OnFace (1/6) x := by
  have hg := (ground_shift hx (0:Fin 6)).1
  obtain ⟨t,ht,he⟩ := closed_contacts_are_face hg
    (fun i _ => physical_uniform_endpoint hg i.castSucc)
  exact ⟨0,t,ht,he⟩

/-- Only the two published small-floor rectangles lie outside the union of
the closed certificate roots. The narrow and broad ranges overlap at width 8. -/
def SmallRectangle (s h : ℝ) : Prop :=
  (8 ≤ s ∧ s ≤ 9 ∧ h ≤ 7/100) ∨ (799/100 ≤ s ∧ s ≤ 801/100 ∧ h ≤ 1/10)

theorem full_strip_from_exclusions_and_small (excluded : ∀ slab b i, RowExcluded slab b i)
    {s h : ℝ} (hs : s ∈ Icc (799/100) 9) (hh : h ∈ Ioc 0 (1/6))
    (small : SmallRectangle s h → ∀ x, IsGroundState positiveSix h s x → OnFace h x)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) : OnFace h x := by
  rcases lt_or_eq_of_le hh.2 with h6 | he
  · have hs0 : 0 < s := by linarith only [hs.1]
    by_cases hn : s < 8
    · by_cases hsmall : h ≤ 1/10
      · exact small (.inr ⟨hs.1, by linarith, hsmall⟩) x hx
      · apply packed_of_leaf_checker .narrow (excluded _) hs0 _ hh.1.le _ h6 x hx
        · change ((799/100:ℚ):ℝ) ≤ s ∧ s ≤ ((801/100:ℚ):ℝ)
          norm_num
          exact ⟨hs.1,by linarith⟩
        · have H : Slab.narrow.edge 0 = 1/10 := by norm_num [Slab.edge]
          rw [H]; norm_num; linarith
    · by_cases hsmall : h ≤ 7/100
      · exact small (.inl ⟨le_of_not_gt hn, hs.2, hsmall⟩) x hx
      · by_cases hl : s ≤ 17/2
        · apply packed_of_leaf_checker .lower (excluded _) hs0 _ hh.1.le _ h6 x hx
          · change ((8:ℚ):ℝ) ≤ s ∧ s ≤ ((17/2:ℚ):ℝ)
            norm_num
            exact ⟨le_of_not_gt hn,hl⟩
          · have H : Slab.lower.edge 0 = 7/100 := by norm_num [Slab.edge]
            rw [H]; norm_num; linarith
        · apply packed_of_leaf_checker .upper (excluded _) hs0 _ hh.1.le _ h6 x hx
          · change ((17/2:ℚ):ℝ) ≤ s ∧ s ≤ ((9:ℚ):ℝ)
            norm_num
            exact ⟨le_of_not_ge hl,hs.2⟩
          · have H : Slab.upper.edge 0 = 7/100 := by norm_num [Slab.edge]
            rw [H]; norm_num; linarith
  · subst h
    exact uniform_endpoint_onFace x hx

theorem full_strip_from_rows_and_small (rows : ∀ slab, RowsAccepted slab)
    {s h : ℝ} (hs : s ∈ Icc (799/100) 9) (hh : h ∈ Ioc 0 (1/6))
    (small : SmallRectangle s h → ∀ x, IsGroundState positiveSix h s x → OnFace h x)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) : OnFace h x :=
  full_strip_from_exclusions_and_small
    (fun slab b i => rowExcluded_of_checkRow slab b i (rows slab b i)) hs hh small x hx

private theorem normalized_sites {h : ℝ} {x : Fin 6 → ℝ} {k : Fin 6} {t : ℝ}
    (hr : RepresentsFace h x k t) :
    (fun i => shiftLifts positiveSix x k i - shiftLifts positiveSix x k 0) = sites h t := by
  funext i
  linarith only [hr i]

theorem represents_energy {s h : ℝ} {x : Fin 6 → ℝ} {k : Fin 6} {t : ℝ}
    (hr : RepresentsFace h x k t) : imageEnergy s (sites h t) = imageEnergy s x := by
  rw [← normalized_sites hr, imageEnergy_sub_const, imageEnergy_shiftLifts _ (by decide)]

private theorem represents_feasible {h : ℝ} {x : Fin 6 → ℝ} {k : Fin 6} {t : ℝ}
    (hr : RepresentsFace h x k t) (ht : feasible h t) : Feasible positiveSix h x := by
  apply (feasible_shiftLifts_iff positiveSix h x k).mp
  have H := (all_gaps_iff h t).mpr ht
  rw [← normalized_sites hr] at H
  intro i
  simpa only [gap_sub_const] using H i

/-- If every minimizer is on the packed face, every physical minimum is
a face minimum and conversely every minimizing displacement and every one
of its cyclic representatives attains the minimum over the whole simplex. -/
theorem full_classification_of_onFace {s h : ℝ} (hs : 0 < s) (hh : h ∈ Ioc 0 (1/6))
    (reduction : ∀ x, IsGroundState positiveSix h s x → OnFace h x) (x : Fin 6 → ℝ) :
    IsGroundState positiveSix h s x ↔
      ∃ k t, minimizesEnergy s h t ∧ RepresentsFace h x k t := by
  constructor
  · intro hx
    obtain ⟨k,t,ht,hr⟩ := reduction x hx
    refine ⟨k,t,⟨ht,?_⟩,hr⟩
    intro v hv
    change imageEnergy s (sites h t) ≤ imageEnergy s (sites h v)
    rw [represents_energy hr]
    exact hx.2 _ ((all_gaps_iff h v).mpr hv)
  · rintro ⟨k,t,ht,hr⟩
    obtain ⟨y,hy⟩ := exists_groundState positiveSix hh.1.le (by simpa using hh.2) hs
    obtain ⟨j,u,hu,hr'⟩ := reduction y hy
    refine ⟨represents_feasible hr ht.1,fun z hz ↦ ?_⟩
    have htu : imageEnergy s (sites h t) ≤ imageEnergy s (sites h u) := ht.2 u hu
    rw [represents_energy hr, represents_energy hr'] at htu
    exact htu.trans (hy.2 z hz)

#print axioms rowExcluded_of_tree
#print axioms packed_of_leaf_checker

end GaussianChains.Band

