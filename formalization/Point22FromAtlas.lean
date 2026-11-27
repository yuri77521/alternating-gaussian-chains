import Point22AtlasVariations
import Point22AtlasCanonical
import Point22AtlasReplay
import Point22Assembly
import CertRootWitness

/-! Lift a verified complete atlas to all physical six-site cells. -/

namespace GaussianChains.Point22.Atlas

open Set GaussianChains.Cert GaussianChains.ImageBounds Root22

theorem starts_spanTicks (w : Word) (x : Fin 6 → ℝ) (hx : Feasible (by decide) (1/1000) x) :
    SpanTicks w (ticks (starts w x)) := by
  intro i j hij
  have hmon := (base_mono w i j hij.1 hij.2).2
  have he := active_base w j hij.2
  have hm : startLabel w i ≤ startLabel w j := hmon
  have hb : span w i j ≤ 6 := by
    dsimp [span]
    change base w j - base w i ≤ 6
    omega
  obtain ⟨hg,hg'⟩ := starts_pair_distance w x hx i j hij.1 hij.2
  rw [Nat.cast_sub hb]
  simp only [span,Nat.cast_sub hm,Nat.cast_ofNat,ticks]
  constructor <;> linarith

private theorem raw_local_shape (y : Fin 6 → ℝ) (h0 : y 0 = 0)
    (ht : localTarget.Mem (ticks y)) :
    ∃ p ∈ localDomain, ∀ i, placed .threeOneOneOne y i = cell3111 (1/1000) p i + 1/1000 := by
  let p : Point := (y 1-1/1000,y 2-1/1000,y 3-1/1000)
  have h₁ := ht 1; have h₂ := ht 2; have h₃ := ht 3
  norm_num [localTarget,Interval.Mem,ticks] at h₁ h₂ h₃
  refine ⟨p,?_,?_⟩
  · intro i
    fin_cases i <;> simp [p,side] <;> constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2]
  · intro i
    fin_cases i
    · change y 0+((0:ℕ):ℝ)/1000 = -(1/1000:ℝ)+1/1000
      norm_num [h0]
    · change y 0+((1:ℕ):ℝ)/1000 = 0+1/1000
      norm_num [h0]
    · change y 0+(2:ℝ)/1000 = 1/1000+1/1000
      norm_num [h0]
    · change y 1+((0:ℕ):ℝ)/1000 = y 1-1/1000+1/1000
      ring
    · change y 2+((0:ℕ):ℝ)/1000 = y 2-1/1000+1/1000
      ring
    · change y 3+((0:ℕ):ℝ)/1000 = y 3-1/1000+1/1000
      ring

theorem physical_localize_of_admissible_replays {lookup : Lookup} {internal : Word → Interval}
    {witness : Interval}
    (hr : ∀ (a b : ℕ) (j : Order) (l r : ℕ), l ≤ r → r ≤ 32000 → ∀ t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000),
      (lookup a b j l r).Mem (blockValue a b (orderIndex j) t))
    (hi : ∀ w, (internal w).Mem (internalScore w))
    (hw : witness.Mem (pairScore 22 (fun i => (witnessX i:ℝ))))
    (checked : ∀ w (z : Fin 6 → ℝ), IsGroundState (by decide) (1/1000) 22 z →
      CanonicalBlockCut w (gap (by decide) z) →
      replay w (boundsFrom lookup internal witness w) (rootBox w) (tree w) = true)
    (x : Fin 6 → ℝ) (hx : IsGroundState (by decide) (1/1000) 22 x) : LocalizedAt x (1/1000) := by
  obtain ⟨w,k,rev,hcanon⟩ := physical_canonical_cut x
  let z := transformed x k rev
  let y := starts w z
  have hz : IsGroundState (by decide) (1/1000) 22 z := ground_transformed hx k rev
  have hs : pairScore 22 z = atlasScore w y (internalScore w) := by
    have hrel := funext (physical_placed_of_cuts w z hz.1 hcanon.1)
    calc
      _ = pairScore 22 (fun p => placed w y p + z 0) := congrArg (pairScore 22) hrel
      _ = pairScore 22 (placed w y) := by simp [pairScore]
      _ = _ := atlasScore_placed w y
  have hwit := (imageEnergy_le_iff_pairScore_ge (by decide) 22 z _).mp (hz.2 _ witnessX_feasible)
  rw [hs] at hwit
  have hm : meshToPhysical (ticks y) = y := by funext i; simp [meshToPhysical,ticks]
  obtain ⟨he,hlocal⟩ := classify_of_replay hr (hi w) hw (starts_orderedTicks w z hz.1)
    (starts_canonicalTicks w z hz.1 hcanon) (starts_spanTicks w z hz.1) (starts_rootBox w z hz.1)
    (fun q => by
      rw [hm]
      exact realQuantity_necessary w y _ _ hwit (ground_atlas_local_max w z hz hcanon.1) q) (checked w z hz hcanon)
  subst w
  obtain ⟨p,hp,hy⟩ := raw_local_shape y (starts_zero _ z) hlocal
  have hpz (i : Fin 6) : z i = cell3111 (1/1000) p i + (z 0+1/1000) := by
    have h := physical_placed_of_cuts _ z hz.1 hcanon.1 i
    change z i = placed .threeOneOneOne y i + z 0 at h
    rw [hy] at h
    linarith
  have hg : gap (by decide) z = gap (by decide) (cell3111 (1/1000) p) := by
    conv_lhs => rw [funext hpz]
    funext i
    rw [six_gap_eq,six_gap_eq]
    simp [cyclicGap]
  refine ⟨p,hp,(if rev then k else -k),rev,?_⟩
  funext i
  let j := edgeIndex (if rev then k else -k) rev i
  have hinv : edgeIndex k rev j = i :=
    (by decide : ∀ k : Fin 6, ∀ rev : Bool, ∀ i,
      edgeIndex k rev (edgeIndex (if rev then k else -k) rev i) = i) k rev i
  have he := transformed_gap x k j rev
  change gap (by decide) z j = _ at he
  rw [hinv,hg] at he
  exact he.symm.trans (transformed_gap (cell3111 (1/1000) p) _ i rev).symm

theorem physical_localize_of_replay {lookup : Lookup} {internal : Word → Interval}
    {witness : Interval}
    (hr : ∀ (a b : ℕ) (j : Order) (l r : ℕ), l ≤ r → r ≤ 32000 → ∀ t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000),
      (lookup a b j l r).Mem (blockValue a b (orderIndex j) t))
    (hi : ∀ w, (internal w).Mem (internalScore w))
    (hw : witness.Mem (pairScore 22 (fun i => (witnessX i:ℝ))))
    (checked : ∀ w, replay w (boundsFrom lookup internal witness w) (rootBox w) (tree w) = true)
    (x : Fin 6 → ℝ) (hx : IsGroundState (by decide) (1/1000) 22 x) : LocalizedAt x (1/1000) :=
  physical_localize_of_admissible_replays hr hi hw (fun w _ _ _ => checked w) x hx

end GaussianChains.Point22.Atlas
