import Point22AtlasScores
import Point22AtlasScoreData
import Point22AtlasClaims
import CertRootValue

/-! Independent image enclosures for all retained value nodes used by the
constant parts of the width-22 atlas. These fifteen samples suffice for
every internal score and for the score of the feasible trial X. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds

private def checkRow (r : ℕ × Interval) : Bool :=
  let x : ℚ := r.1 / 32000
  let b := Root22.kernelBox (x,x)
  decide (x ≤ 1 ∧ r.2.lo ≤ b.1 ∧ b.2 ≤ r.2.hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem rows_checked : scoreRows.all checkRow = true := by decide +kernel

private theorem row_sound {r : ℕ × Interval} (hr : r ∈ scoreRows) :
    r.2.Mem (kernel 22 ((r.1:ℝ)/32000)) := by
  let q : ℚ := r.1 / 32000
  have h := List.all_eq_true.mp rows_checked r hr
  change decide (q ≤ 1 ∧ r.2.lo ≤ (Root22.kernelBox (q,q)).1 ∧
    (Root22.kernelBox (q,q)).2 ≤ r.2.hi) = true at h
  obtain ⟨hq, hl, hu⟩ := of_decide_eq_true h
  have hx : |(q:ℝ)| ≤ 1 := by
    have hq' : 0 ≤ (q:ℝ) := by dsimp [q]; positivity
    rw [abs_of_nonneg hq']
    exact_mod_cast hq
  have H := Root22.kernelBox_sound (d := (q,q)) (x := (q:ℝ)) ⟨le_rfl,le_rfl⟩ hx
  have he : (q:ℝ) = (r.1:ℝ)/32000 := by simp [q]
  rw [← he]
  exact ⟨(by exact_mod_cast hl : (r.2.lo:ℝ) ≤ ((Root22.kernelBox (q,q)).1:ℝ)).trans H.1,
    H.2.trans (by exact_mod_cast hu)⟩

private def valueFromRows (p : ℕ) (fallback : Interval) : List (ℕ × Interval) → Interval
  | [] => fallback
  | (k,I) :: rest => if k=p then I else valueFromRows p fallback rest

private theorem valueFromRows_mem (p : ℕ) (fallback : Interval) (rows : List (ℕ × Interval))
    (h : ∀ r ∈ rows, r.2.Mem (kernel 22 ((r.1:ℝ)/32000)))
    (hf : fallback.Mem (kernel 22 ((p:ℝ)/32000))) :
    (valueFromRows p fallback rows).Mem (kernel 22 ((p:ℝ)/32000)) := by
  induction rows with
  | nil => exact hf
  | cons r rs ih =>
    rcases r with ⟨k,I⟩
    by_cases he : k=p
    · subst k
      simpa only [valueFromRows, if_pos rfl] using h (p,I) (by simp)
    · simp only [valueFromRows, if_neg he]
      exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr))

def scoreNode (ord : Order) (p : ℕ) : Interval :=
  match ord with
  | .value => valueFromRows p (atlasNode .value p) scoreRows
  | .first => atlasNode .first p
  | .second => atlasNode .second p

theorem scoreNode_sound (o : Order) (p : ℕ) (hp : p < 32000) :
    (scoreNode o p).Mem (mode (orderIndex o) ((p:ℝ)/32000)) := by
  cases o with
  | value => exact valueFromRows_mem _ _ _ (fun _ => row_sound) (atlasNode_sound _ _ hp)
  | first => exact atlasNode_sound _ _ hp
  | second => exact atlasNode_sound _ _ hp

set_option maxHeartbeats 0 in
private theorem internal_eq (w : Word) : internalFrom scoreNode w = internalTicks w := by
  cases w <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem witness_eq : witnessFrom scoreNode = witnessTicks := by decide +kernel

/-- The archived upper and lower integer endpoints enclose the actual real
internal score for every one of the twelve contact words. -/
theorem internalTicks_sound (w : Word) : (internalTicks w).Mem (internalScore w) := by
  rw [← internal_eq]
  exact internalFrom_sound scoreNode_sound w

/-- Both endpoints for the signed unordered-pair score of X, including the
lower comparison threshold -200132043312/10^11 used by the search. -/
theorem witnessTicks_sound : witnessTicks.Mem (pairScore 22 fun i => (Root22.witnessX i : ℝ)) := by
  rw [← witness_eq]
  exact witnessFrom_sound scoreNode_sound

#print axioms internalTicks_sound
#print axioms witnessTicks_sound

end GaussianChains.Point22.Atlas
