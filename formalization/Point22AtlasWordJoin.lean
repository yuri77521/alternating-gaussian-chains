import Point22AtlasTree
import Mathlib.Data.Fin.VecNotation

/-! Joining independently replayed pieces of the original atlas. Every boundary
box is recomputed from its parent; each tip runs the original replay procedure. -/

namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

def endpointsBox (p0 p1 p2 p3 p4 p5 : ℤ × ℤ) : Box 6 :=
  fun i => let p := (![p0,p1,p2,p3,p4,p5] : Fin 6 → ℤ × ℤ) i
           ⟨p.1,p.2⟩

def leftSubtree : Tree 6 → Tree 6
  | .split _ _ left _ => left
  | _ => .hole

def rightSubtree : Tree 6 → Tree 6
  | .split _ _ _ right => right
  | _ => .hole

def splitMatches (w : Word) (B BL BR : Box 6) : Tree 6 → Bool
  | .split i t _ _ =>
    let C := narrow w B
    decide ((C i).lo ≤ t ∧ t ≤ (C i).hi ∧
      (∀ k, C.Left i t k = BL k) ∧ (∀ k, C.Right i t k = BR k))
  | _ => false

theorem replay_join_checked (w : Word) {bounds : Box 6 → Quantity → Interval}
    (B BL BR : Box 6) (T : Tree 6)
    (joins : splitMatches w B BL BR T = true)
    (left : replay w bounds BL (leftSubtree T) = true)
    (right : replay w bounds BR (rightSubtree T) = true) :
    replay w bounds B T = true := by
  cases T with
  | hole | localDomain | leaf => simp [splitMatches] at joins
  | split i t lo hi =>
    obtain ⟨h₁,h₂,hL,hR⟩ := of_decide_eq_true joins
    simp only [replay, Bool.and_eq_true, decide_eq_true_eq]
    rw [funext hL, funext hR]
    exact ⟨⟨⟨h₁,h₂⟩,left⟩,right⟩

end GaussianChains.Point22.Atlas
