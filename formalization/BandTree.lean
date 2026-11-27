import BandOracle
import StripGeometry
import StripSupports

/-! Width-strip certificate language. The selected support is checked at every
transfer. Splits use the contracted chamber; both closed children contain
their common boundary. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Finset Interval

inductive Terminal where
  | value
  | gradient (k : Fin 5)
  | curvature (i j : Fin 6)
  deriving Repr

inductive Cover (Witness : Type) where
  | hole
  | empty
  | leaf (reason : Witness)
  | split (i : Fin 6) (cut : ℚ) (left right : Cover Witness)
  deriving Repr

def allBounds (B : Box 6) (side : Bool) : ℚ :=
  ∑ i, if side then (B i).hi else (B i).lo

/-- The frozen search first corrects all lower ends, then uses these new ends
when correcting the upper ends. -/
def raiseLower (B : Box 6) : Box 6 := fun i =>
  ⟨max (B i).lo (1 - allBounds B true + (B i).hi), (B i).hi⟩

def lowerUpper (B : Box 6) : Box 6 := fun i =>
  ⟨(B i).lo, min (B i).hi (1 - allBounds B false + (B i).lo)⟩

private theorem complement_le {B : Box 6} {u : Fin 6 → ℝ}
    (hm : B.Mem u) (hs : ∑ i, u i = 1) (k : Fin 6) :
    1 - (allBounds B true : ℝ) + ((B k).hi : ℝ) ≤ u k ∧
    u k ≤ 1 - (allBounds B false : ℝ) + ((B k).lo : ℝ) := by
  classical
  let rest := (univ : Finset (Fin 6)).erase k
  have hsum (v : Fin 6 → ℝ) : (∑ j ∈ rest, v j) + v k = ∑ j, v j :=
    sum_erase_add _ _ (mem_univ k)
  have hh := sum_le_sum (s:=rest) (fun j _ => (hm j).2)
  have hl := sum_le_sum (s:=rest) (fun j _ => (hm j).1)
  have hu := hsum u
  rw [hs] at hu
  simp [allBounds]
  constructor <;> linarith only [hh,hl,hu,hsum (fun j => ((B j).hi : ℝ)),
    hsum (fun j => ((B j).lo : ℝ))]

theorem raiseLower_mem {B : Box 6} {u : Fin 6 → ℝ}
    (hm : B.Mem u) (hs : ∑ i, u i = 1) : (raiseLower B).Mem u := by
  intro i
  exact ⟨by simpa [raiseLower] using max_le (hm i).1 (complement_le hm hs i).1,
    (hm i).2⟩

theorem lowerUpper_mem {B : Box 6} {u : Fin 6 → ℝ}
    (hm : B.Mem u) (hs : ∑ i, u i = 1) : (lowerUpper B).Mem u := by
  intro i
  exact ⟨(hm i).1, by simpa [lowerUpper] using le_min (hm i).2 (complement_le hm hs i).2⟩

def contract (B : Box 6) : Box 6 :=
  let C := lowerUpper (raiseLower B)
  -- This fold sets the distinguished lower end to the largest lower end and
  -- caps each upper end by the distinguished upper end.
  (List.finRange 6).foldl (fun D j => D.tightenLargest 5 j) C

theorem contract_mem {B : Box 6} {u : Fin 6 → ℝ} (hm : B.Mem u)
    (hs : ∑ i, u i = 1) (hmax : ∀ i, u i ≤ u 5) : (contract B).Mem u := by
  have fold (L : List (Fin 6)) (C : Box 6) (hc : C.Mem u) :
      (L.foldl (fun D j => D.tightenLargest 5 j) C).Mem u := by
    induction L generalizing C with
    | nil => exact hc
    | cons j js ih => exact ih _ (Box.tightenLargest_mem hc (hmax j))
  exact fold _ _ (lowerUpper_mem (raiseLower_mem hm hs) hs)

def void (B : Box 6) : Bool :=
  B.emptyB || decide (1 < allBounds B false ∨ allBounds B true < 1)

theorem void_sound {B : Box 6} (v : void B = true) {u : Fin 6 → ℝ}
    (hm : B.Mem u) (hs : ∑ i, u i = 1) : False := by
  rcases Bool.or_eq_true_iff.mp v with he | he
  · exact Box.emptyB_sound he u hm
  · have h := of_decide_eq_true he
    have hlo := Finset.sum_le_sum (s := univ) (fun i _ => (hm i).1)
    have hhi := Finset.sum_le_sum (s := univ) (fun i _ => (hm i).2)
    rw [hs] at hlo hhi
    rcases h with h | h
    · exact (not_lt_of_ge hlo) (by exact_mod_cast (by simpa [allBounds] using h :
         (1:ℚ) < ∑ i, (B i).lo))
    · exact (not_lt_of_ge hhi) (by exact_mod_cast (by simpa [allBounds] using h :
         (∑ i, (B i).hi) < (1:ℚ)))

def check {W : Type} (test : Box 6 → W → Bool) (B : Box 6) : Cover W → Bool
  | .hole => false
  | .empty => void (contract (contract B))
  | .leaf reason => test (contract (contract B)) reason
  | .split i cut l r =>
    let C := contract (contract B)
    decide ((C i).lo ≤ cut ∧ cut ≤ (C i).hi) &&
      check test (C.Left i cut) l && check test (C.Right i cut) r

/-- Genuine candidates pass every chamber contraction, including a tie for largest.
Leaves are obliged to eliminate the actual candidate point in the contracted box. -/
theorem check_sound {W : Type} {test : Box 6 → W → Bool} {P : (Fin 6 → ℝ) → Prop}
    (leaf : ∀ B r u, test B r = true → B.Mem u → P u → False)
    (t : Cover W) (B : Box 6) (hc : check test B t = true)
    {u : Fin 6 → ℝ} (hbox : B.Mem u) (hs : ∑ i, u i = 1)
    (hm : ∀ i, u i ≤ u 5) : ¬P u := by
  intro hp
  induction t generalizing B with
  | hole => simp [check] at hc
  | empty => exact void_sound hc (contract_mem (contract_mem hbox hs hm) hs hm) hs
  | leaf r => exact leaf _ _ u hc (contract_mem (contract_mem hbox hs hm) hs hm) hp
  | split i cut l r il ir =>
    simp only [check, Bool.and_eq_true] at hc
    rcases Box.split_cover (contract_mem (contract_mem hbox hs hm) hs hm) i cut with h | h
    · exact il _ hc.1.2 h
    · exact ir _ hc.2 h

end GaussianChains.Band
