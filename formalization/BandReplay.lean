import BandLeaves
import Mathlib.Data.Fin.VecNotation

/-! The packet contains postfix trees. Parsing failure or trailing subtrees
reject the packet. Every accepted packet must pass the real box checker. -/
namespace GaussianChains.Band
open GaussianChains.Strip GaussianChains.Cert Interval

inductive Witness where
  | transfer (r : Terminal)
  | centered (c : Fin 6 → ℚ)
  deriving Repr

def grid (n : ℕ) : ℚ := (n:ℚ)/8192

private def pushInstruction (stack : List (Cover Witness)) (token : String) :
    Option (List (Cover Witness)) := do
  let xs ← (token.splitOn ",").mapM String.toNat?
  match xs with
  | [0] => return .empty :: stack
  | [1,k] =>
    if hk : k < 5 then return .leaf (.transfer (.gradient ⟨k,hk⟩)) :: stack else none
  | [2,i,j] =>
    if hi : i < 6 then
      if hj : j < 6 then return .leaf (.transfer (.curvature ⟨i,hi⟩ ⟨j,hj⟩)) :: stack else none
    else none
  | [3,a,b,c,d,e,f] =>
    return .leaf (.centered ![grid a, grid b, grid c, grid d, grid e, grid f]) :: stack
  | [4,k,mid] =>
    if hk : k < 6 then
      match stack with
      | right :: left :: rest => return .split ⟨k,hk⟩ (grid mid) left right :: rest
      | _ => none
    else none
  | _ => none

def decode (data : String) : Option (Cover Witness) := do
  let trees ← (data.splitOn ";").foldlM pushInstruction []
  match trees with
  | [tree] => return tree
  | _ => none

def checkPacket (test : Box 6 → Witness → Bool) (B : Box 6) (data : String) : Bool :=
  match decode data with
  | some tree => check test B tree
  | none => false

theorem checkPacket_sound {test : Box 6 → Witness → Bool} {P : (Fin 6 → ℝ) → Prop}
    (leaf : ∀ B r u, test B r = true → B.Mem u → P u → False)
    (B : Box 6) (data : String) (hc : checkPacket test B data = true)
    {u : Fin 6 → ℝ} (hb : B.Mem u) (hs : ∑ i, u i = 1) (hm : ∀ j, u j ≤ u 5) : ¬ P u := by
  unfold checkPacket at hc
  split at hc
  · exact check_sound leaf _ _ hc hb hs hm
  · contradiction

/-- The 18 support roots are fixed by the problem; the packet cannot replace
the starting box with a smaller one. -/
def initial (A : Support) : Box 6 := fun i =>
  ⟨0, if i = 5 then 1 else if ∃ k ∈ A, k.castSucc = i then 1/2 else 0⟩

theorem initial_mem {u : Fin 6 → ℝ} (hu : simplex u) (hm : ∀ j, u j ≤ u 5) :
    (initial (activeSupport u)).Mem u := by
  intro i
  refine ⟨by simpa [initial] using hu.1 i, ?_⟩
  by_cases h : i = 5
  · subst i
    have hl := Finset.single_le_sum (f:=u) (fun j _ => hu.1 j) (Finset.mem_univ (5:Fin 6))
    simpa [initial, hu.2] using hl
  · by_cases ha : ∃ k ∈ activeSupport u, k.castSucc = i
    · simpa [initial, h, ha] using free_coordinate_le_half hu h (hm i)
    · obtain ⟨k, hk⟩ : ∃ k : Fin 5, k.castSucc = i := by
        exact ⟨⟨i.val, by have := i.isLt; have : i.val ≠ 5 := fun hl => h (Fin.ext hl); omega⟩, rfl⟩
      have hz : ¬0 < u i := fun hp => ha ⟨k,(mem_active_iff u k).2 (hk ▸ hp), hk⟩
      simpa [initial, h, ha] using le_of_not_gt hz

end GaussianChains.Band
