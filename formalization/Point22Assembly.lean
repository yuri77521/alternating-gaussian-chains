import Point22Physical
import Point22Score
import ChainMinimum

/-! The logical interface between exhaustive localization and the physical
width-22 classification. The hypotheses expose the two separate analytical
inputs: capture of every minimizer and strict uniqueness in the capture domain. -/

namespace GaussianChains.Point22

open Set

/-- Localization is modulo all cyclic relabelings, including odd shifts. -/
def SameGeometry (x y : Fin 6 → ℝ) : Prop :=
  ∃ k : Fin 6, ∃ rev : Bool, gap (by decide) x = gap (by decide) (transformed y k rev)

theorem geometry_energy {x y : Fin 6 → ℝ} (hg : SameGeometry x y) (s : ℝ) :
    imageEnergy s x = imageEnergy s y := by
  obtain ⟨k,rev,he⟩ := hg
  rw [← imageEnergy_sitesOfGaps_gap (by decide) s x, he, imageEnergy_sitesOfGaps_gap]
  cases rev <;> simp [transformed, imageEnergy_reflectLifts (N:=6) (by decide) (by decide),
    imageEnergy_shiftLifts (N:=6) (by decide) (by decide)]

theorem geometry_fixed_line_iff (x : Fin 6 → ℝ) (h R : ℝ) :
    SameGeometry x (sites h R) ↔ ∃ k : Fin 6, gap (by decide) x = rotate (gapWord h R) k := by
  have href (i : Fin 6) : gapWord h R i = gapWord h R (1-i) := by fin_cases i <;> rfl
  constructor
  · rintro ⟨k,rev,he⟩
    cases rev with
    | false =>
      refine ⟨k,funext fun i => ?_⟩
      simpa [rotate, transformed_gap, physical_sites_gaps, edgeIndex] using congrFun he i
    | true =>
      refine ⟨2-k,funext fun i => ?_⟩
      have hk := congrFun he i
      rw [transformed_gap,physical_sites_gaps,href (edgeIndex k true i)] at hk
      exact hk.trans (congrArg (gapWord h R) ((by decide :
        ∀ i k : Fin 6, 1-edgeIndex k true i = i+(2-k)) i k))
  · rintro ⟨k,hk⟩
    exact ⟨k,false,funext fun i => by
      simpa [rotate,transformed_gap,physical_sites_gaps,edgeIndex] using congrFun hk i⟩

def LocalizedAt (x : Fin 6 → ℝ) (h : ℝ) : Prop :=
  ∃ p ∈ localDomain, SameGeometry x (cell3111 h p)

/-- The only global premise is localization of all minimizers in the certified
closed domain. No existence, symmetry or orbit multiplicity is required of
that premise. -/
theorem classification_of_localization {R : ℝ}
    (hR : 2*(1/1000 : ℝ) < R) (hR' : R < 1/2-(1/1000 : ℝ))
    (localize : ∀ x : Fin 6 → ℝ, IsGroundState (by decide) (1/1000) 22 x →
      LocalizedAt x (1/1000))
    (strict : ∀ p ∈ localDomain, p ≠ (R,1/2,1-R) →
      imageEnergy 22 (sites (1/1000) R) < imageEnergy 22 (cell3111 (1/1000) p)) :
    (∀ x : Fin 6 → ℝ, IsGroundState (by decide) (1/1000) 22 x ↔
      ∃ k : Fin 6, gap (by decide) x = rotate (gapWord (1/1000) R) k) ∧
    minimumEnergy (N:=6) (by decide) (1/1000) 22 = imageEnergy 22 (sites (1/1000) R) := by
  let Z := sites (1/1000) R
  have href : Feasible (by decide) (1/1000) Z := physical_sites_feasible _ _ hR hR'
  have forward (x : Fin 6 → ℝ) (hx : IsGroundState (by decide) (1/1000) 22 x) :
      SameGeometry x Z := by
    obtain ⟨p,hp,hgeom⟩ := localize x hx
    have hE := geometry_energy hgeom 22
    have he := hx.2 Z href
    have hp' : p = (R,1/2,1-R) := by
      by_contra hn
      exact (strict p hp hn).not_ge (hE ▸ he)
    subst p
    exact hgeom
  obtain ⟨z,hz⟩ := exists_groundState (N:=6) (by decide) (h:=1/1000) (s:=22)
    (by norm_num) (by norm_num) (by norm_num)
  have hzE := geometry_energy (forward z hz) 22
  constructor
  · intro x
    constructor
    · intro hx
      exact (geometry_fixed_line_iff _ _ _).mp (forward x hx)
    · rintro ⟨k,hk⟩
      have hxE := geometry_energy ((geometry_fixed_line_iff _ _ _).mpr ⟨k,hk⟩) 22
      refine ⟨?_, fun y hy => ?_⟩
      · intro i
        rw [show gap (by decide) x i = _ from congrFun hk i]
        exact (feasible_gapWord _ _ hR hR').1 _
      · rw [hxE,← hzE]
        exact hz.2 _ hy
  · exact (groundState_energy_eq_minimum hz).symm.trans hzE

end GaussianChains.Point22


