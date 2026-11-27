import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Classification of the actual contact support at the width-22 parameter point.
A cut is a *strictly slack* gap; equality is a contact, including the wrap gap.
The class representative ends a packed block exactly at a proper prefix sum
minus one (and also at the final edge). -/

namespace GaussianChains.Point22

inductive Word where
  | six | threeThree | fourTwo | fiveOne | twoTwoTwo | threeTwoOne | fourOneOne
  | twoOneTwoOne | twoTwoOneOne | singletons | twoOneOneOneOne | threeOneOneOne
  deriving Repr, DecidableEq, Inhabited

def Word.blocks : Word → List ℕ
  | .six => [6]
  | .threeThree => [3,3]
  | .fourTwo => [4,2]
  | .fiveOne => [5,1]
  | .twoTwoTwo => [2,2,2]
  | .threeTwoOne => [3,2,1]
  | .fourOneOne => [4,1,1]
  | .twoOneTwoOne => [2,1,2,1]
  | .twoTwoOneOne => [2,2,1,1]
  | .singletons => [1,1,1,1,1,1]
  | .twoOneOneOneOne => [2,1,1,1,1]
  | .threeOneOneOne => [3,1,1,1]

theorem Word.sum_blocks (w : Word) : w.blocks.sum = 6 := by cases w <;> decide

theorem Word.pos_blocks (w : Word) : ∀ k ∈ w.blocks, 0 < k := by cases w <;> decide

/-- A true bit ends one maximal packed block. -/
def Word.cuts (w : Word) (i : Fin 6) : Bool :=
  (w.blocks.scanl (· + ·) 0).contains (i.val + 1)

def words : List Word :=
  [.six, .threeThree, .fourTwo, .fiveOne, .twoTwoTwo, .threeTwoOne, .fourOneOne,
   .twoOneTwoOne, .twoTwoOneOne, .singletons, .twoOneOneOneOne, .threeOneOneOne]

def edgeIndex (k : Fin 6) (reverse : Bool) (i : Fin 6) : Fin 6 :=
  if reverse then k - 1 - i else i + k

def matchesWord (m : Fin 6 → Bool) (w : Word) : Bool :=
  (List.finRange 6).any fun k =>
    [false,true].any fun rev =>
      (List.finRange 6).all fun i => m i == w.cuts (edgeIndex k rev i)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem finite_cover :
    ∀ a b c d e f : Bool, (![a,b,c,d,e,f] : Fin 6 → Bool) = ![false,false,false,false,false,false]
      ∨ (words.filter (matchesWord ![a,b,c,d,e,f])).length = 1 := by


  decide

/-- Every nonempty cut support has exactly one of the twelve block words, up
to cyclic relabeling and reversal. -/
theorem twelve_contact_words (m : Fin 6 → Bool) (hm : ∃ i, m i = true) :
    (words.filter (matchesWord m)).length = 1 := by
  have h : m = ![m 0,m 1,m 2,m 3,m 4,m 5] := by funext i; fin_cases i <;> rfl
  rcases finite_cover (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) with hz | good
  · obtain ⟨i, hi⟩ := hm
    have bad := congrFun (h.trans hz) i
    fin_cases i <;> simp_all
  · rwa [h] 

noncomputable def actualCuts (h : ℝ) (g : Fin 6 → ℝ) (i : Fin 6) : Bool := decide (h < g i)

/-- At the theorem's floor the sum condition forces at least one slack gap.
The classifier therefore includes configurations where some of the gaps just
reached contact, as well as ties among the remaining gaps. -/
theorem actual_word_unique (g : Fin 6 → ℝ) (hface : ∑ i, g i = 1) :
    (words.filter (matchesWord (actualCuts (1/1000) g))).length = 1 := by
  apply twelve_contact_words
  by_contra hn
  push_neg at hn
  have all_le (i : Fin 6) : g i ≤ 1/1000 := by
    have := hn i
    simpa [actualCuts] using this
  simp [Fin.sum_univ_succ] at hface
  linarith [all_le 0, all_le 1, all_le 2, all_le 3, all_le 4, all_le 5]

def Word.twoDisjointContacts (w : Word) : Bool :=
  (List.finRange 6).any fun i => (List.finRange 6).any fun j =>
    !w.cuts i && !w.cuts j && i != j && i+1 != j && j+1 != i

/-- Exactly the nine words of the first row of Table 3 admit two contacts
whose endpoints are four distinct particles. -/
theorem two_disjoint_contacts_iff (w : Word) :
    w.twoDisjointContacts = true ↔
    w ∈ [.six, .threeThree, .fourTwo, .fiveOne, .twoTwoTwo, .threeTwoOne,
         .fourOneOne, .twoOneTwoOne, .twoTwoOneOne] := by cases w <;> decide

end GaussianChains.Point22
