import BandReplay
import BandPackets0
import BandPackets1
import BandPackets2

namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Interval

inductive Slab | narrow | lower | upper
  deriving Repr, DecidableEq

def Slab.anchor : Slab → ℚ | .narrow => 8 | .lower => 33/4 | .upper => 35/4

def Slab.width : Slab → Interval
  | .narrow => ⟨799/100, 801/100⟩
  | .lower => ⟨8, 17/2⟩
  | .upper => ⟨17/2, 9⟩

def Slab.count : Slab → ℕ | .narrow => 14 | _ => 49

def Slab.edge (s : Slab) (i : ℕ) : ℚ :=
  let tick : ℕ := match s with
    | .narrow => if i < 10 then 30000 + 600*i else
        match i with | 10 => 36000 | 11 => 40200 | 12 => 42000 | 13 => 45000 | _ => 50000
    | _ => min 50000 (21000 + 600*i)
  (tick:ℚ)/300000

def Slab.floor (s : Slab) (b : Fin s.count) : Interval := ⟨s.edge b, s.edge (b.val+1)⟩

def Slab.table : Slab → Array (ℕ × String)
  | .narrow => slab0Packets | .lower => slab1Packets | .upper => slab2Packets

def support (i : Fin 18) : Support := offEdgeReps[i.val]'(by decide +revert)

private theorem cover_intervals (f : ℕ → ℚ) {n : ℕ} (hn : n>0)
    {x : ℝ} (hl : (f 0 : ℝ) ≤ x) (hr : x ≤ (f n : ℝ)) :
    ∃ i : Fin n, (f i.val : ℝ) ≤ x ∧ x ≤ (f (i.val+1) : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : x ≤ (f n : ℝ)
    · by_cases hz : n = 0
      · subst n; exact ⟨0,hl,hr⟩
      · obtain ⟨i,l,r⟩ := ih (by omega) h
        exact ⟨i.castSucc,l,r⟩
    · exact ⟨⟨n, Nat.lt_succ_self n⟩,(lt_of_not_ge h).le,hr⟩

theorem Slab.floor_cover (s : Slab) {h : ℝ} (lo : (s.edge 0 : ℝ) ≤ h) (hi : h ≤ 1/6) :
    ∃ b : Fin s.count, (s.floor b).Mem h := by
  have hlast : s.edge s.count = 1/6 := by cases s <;> decide +kernel
  apply cover_intervals s.edge (by cases s <;> decide +kernel) lo
  simpa [hlast] using hi

theorem support_covers {A : Support} (h : A ∈ offEdgeReps) : ∃ i : Fin 18, support i = A := by
  obtain ⟨i,hi,ha⟩ := List.mem_iff_getElem.mp h
  exact ⟨⟨i,by simpa only [offEdgeReps_distinct.1] using hi⟩,ha⟩

def packetCheck (s : Slab) (b : Fin s.count) (i : Fin 18)
    (test : Fin 5 → Box 6 → Witness → Bool) : Bool :=
  match s.table[b.val*18+i.val]? with
  | none => false
  | some (j,data) =>
    if hj : j < 5 then checkPacket (test ⟨j,hj⟩) (initial (support i)) data else false

end GaussianChains.Band
