import Point22Contacts
import Mathlib.Tactic.Ring

/-! Signed symmetry orbits of the localized shape (12). A reflection about the
vertex with index 0 sends edge i to edge -1-i. The extra minus one is important
for the charge-preserving orbit count. -/

namespace GaussianChains.Point22

/-- Increasing representatives before reducing modulo one. -/
noncomputable def sites (h R : ℝ) : Fin 6 → ℝ := ![-h, 0, h, R, 1/2, 1-R]

noncomputable def gapWord (h R : ℝ) : Fin 6 → ℝ := ![h, h, R-h, 1/2-R, 1/2-R, R-h]

def cyclicGap (x : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  x (i+1) - x i + if i = 5 then 1 else 0

theorem sites_gaps (h R : ℝ) : cyclicGap (sites h R) = gapWord h R := by
  funext i
  fin_cases i <;> simp [cyclicGap, sites, gapWord] <;> ring

theorem feasible_gapWord (h R : ℝ) (hR : 2*h < R) (hR' : R < 1/2-h) :
    (∀ i, h ≤ gapWord h R i) ∧ ∑ i, gapWord h R i = 1 := by
  constructor
  · intro i; fin_cases i <;> simp [gapWord] <;> linarith
  · simp [Fin.sum_univ_succ, gapWord]; ring

/-- A charge-preserving isometry may translate/reindex by an even vertex or
reflect about an axis whose vertex index parameter is even. -/
def SameSpecies (g g' : Fin 6 → ℝ) : Prop :=
  ∃ k : Fin 6, k.val % 2 = 0 ∧ ∃ rev : Bool, ∀ i, g' i = g (edgeIndex k rev i)

def rotate {α : Type*} (g : Fin 6 → α) (k i : Fin 6) : α := g (i+k)

private def representativeCuts : Fin 6 → Bool := ![false,false,true,true,true,true]

private theorem cuts_shape (h R : ℝ) (hR : 2*h < R) (hR' : R < 1/2-h) :
    actualCuts h (gapWord h R) = representativeCuts := by
  funext i
  have hA : h < R - h := by linarith
  have hB : h < 1/2 - R := by linarith
  fin_cases i <;> simp [actualCuts, gapWord, representativeCuts, hA] <;> simpa using hB

private theorem finite_parity (k l a : Fin 6) (rev : Bool)
    (ha : a.val % 2 = 0)
    (hm : ∀ i, rotate representativeCuts l i =
        rotate representativeCuts k (edgeIndex a rev i)) :
    k.val % 2 = l.val % 2 := by
  apply (by decide : ∀ k l a : Fin 6, ∀ rev : Bool, a.val % 2 = 0 →
    (∀ i, rotate representativeCuts l i =
        rotate representativeCuts k (edgeIndex a rev i)) → k.val % 2 = l.val % 2) <;>
    assumption

private theorem even_rotation (k l : Fin 6) (h : k.val % 2 = l.val % 2) :
    ∃ a : Fin 6, a.val % 2 = 0 ∧ ∀ i : Fin 6, i + l = (i + a) + k := by
  exact (by decide : ∀ k l : Fin 6, k.val % 2 = l.val % 2 →
    ∃ a : Fin 6, a.val % 2 = 0 ∧ ∀ i : Fin 6, i + l = (i + a) + k) k l h

/-- There are precisely two species-preserving orbits among the rotations of
the shape. Their distinction persists under reflection. -/
theorem shape_orbits_iff (h R : ℝ) (hR : 2*h < R) (hR' : R < 1/2-h)
    (k l : Fin 6) :
    SameSpecies (rotate (gapWord h R) k) (rotate (gapWord h R) l) ↔
    k.val % 2 = l.val % 2 := by
  constructor
  · rintro ⟨a,ha,rev,hm⟩
    apply finite_parity k l a rev ha
    intro i
    have hc := congrFun (cuts_shape h R hR hR') (i+l)
    have hd := congrFun (cuts_shape h R hR hR') (edgeIndex a rev i + k)
    unfold rotate
    rw [← hc, ← hd]
    exact congrArg (fun z : ℝ => decide (h < z)) (hm i)
  · intro hkl
    obtain ⟨a,ha,had⟩ := even_rotation k l hkl
    exact ⟨a,ha,false,fun i => congrArg (gapWord h R) (had i)⟩

theorem unique_middle (h R : ℝ) (hR : 2*h < R) (hR' : R < 1/2-h) (i : Fin 6) :
    (gapWord h R (i-1) = h ∧ gapWord h R i = h) ↔ i = 1 := by
  have hA : R - h ≠ h := by linarith
  have hB : 1/2 - R ≠ h := by linarith
  fin_cases i <;> norm_num [gapWord, hA, hB, show (0-1:Fin 6) = 5 by decide] <;> exact hA

/-- Along the fixed line, the true gap floor, wrap and triple hypotheses all
hold at every real number in the published enclosure. -/
theorem root_interval_shape {R : ℝ}
    (hl : 0.249999032167246504146498709394 < R)
    (hu : R < 0.249999032167246504146498709395) :
    (∀ i, 1/1000 ≤ gapWord (1/1000) R i) ∧
    (∑ i, gapWord (1/1000) R i) = 1 ∧
    ∀ k l : Fin 6,
      SameSpecies (rotate (gapWord (1/1000) R) k) (rotate (gapWord (1/1000) R) l) ↔
      k.val % 2 = l.val % 2 := by
  have h1 : 2*(1/1000 : ℝ) < R := by linarith
  have h2 : R < 1/2-(1/1000 : ℝ) := by linarith
  obtain ⟨hg,hs⟩ := feasible_gapWord _ _ h1 h2
  exact ⟨hg, hs, shape_orbits_iff _ _ h1 h2⟩

end GaussianChains.Point22
