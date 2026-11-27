import BifurcationLaws
import BifurcationNeighborhood
import BifurcationClassification
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The two bifurcating minima in the full constrained simplex. -/

open Filter Set Asymptotics
open scoped Topology
noncomputable section
namespace GaussianChains.Bifurcation
open PackedFace

def chartDomain (h : ℝ) : Set (ℝ × Release) :=
  {p | ∀ i, h ≤ Release.gaps (Release.sites h p.1 p.2) i}

def chartEnergy (h : ℝ) (p : ℝ × Release) : ℝ :=
  imageEnergy 8 (Release.sites h p.1 p.2)

private theorem zero_in_chart {h v : ℝ} (hv : feasible h v) : (v,0) ∈ chartDomain h := by
  apply (Release.feasible_iff h v 0).mpr
  obtain ⟨hl,hu⟩ := abs_le.mp hv
  simp only [Pi.zero_apply, add_zero]
  unfold bound at hl hu
  exact ⟨fun _ => le_rfl,by linarith,by linarith⟩

private theorem chart_feasible_packed {h v : ℝ} {u : Release} (hp : (v,u) ∈ chartDomain h) :
    feasible h v := by
  obtain ⟨hpos,h₁,h₂⟩ := (Release.feasible_iff h v u).mp hp
  unfold feasible bound
  rw [abs_le]
  constructor <;> linarith [hpos 0,hpos 1,hpos 2,hpos 3]

/-- In the inner phase every positive interior stationary displacement is
the packed-face global minimizer up to reflection. -/
theorem stationary_is_face_minimum {h t : ℝ} (hh : hcEight < h)
    (hb : h < criticalFloor true qEight) (ht : t ∈ Ioo 0 (bound h))
    (hstat : deriv (packedEnergy8 h) t = 0) :
    ∀ v, minimizesEnergy 8 h v ↔ v = t ∨ v = -t := by
  have hq : 0 < qEight := Real.exp_pos _
  have hc := (criticalFloor_spec false hq qEight_le).1
  have hh8 : 1/8 < h := hc.1.trans hh
  have h6 := hb.trans (criticalFloor_spec true hq qEight_le).1.2
  have hp : 0 < h := by linarith
  have H := (closed_face_energy_table (by norm_num : (0:ℝ)<8) qEight_le hp h6.le).2.2.1 hh hb
  obtain ⟨t₀,ht₀,H₀,H⟩ := H
  let w := 2*Real.pi
  let C := 4*Real.sqrt (Real.pi/8)*qEight/6
  have hrange (u : ℝ) : coord u ∈ Icc 0 2 := by
    unfold coord
    constructor <;> linarith [Real.cos_le_one (2*Real.pi*u),Real.neg_one_le_cos (2*Real.pi*u)]
  have hforce := deriv_energy_displacement (s := 8) (by norm_num) qEight_le h t
  change deriv (packedEnergy8 h) t = C*(phiD qEight h (coord t)*(w*Real.sin (w*t))) at hforce
  have hprod := hforce.symm.trans hstat
  have hC : 0 < C := by dsimp [C,qEight]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have ht' : t < 1/2 := lt_trans ht.2 (by unfold bound; linarith)
  have hsin := Real.sin_pos_of_pos_of_lt_pi (mul_pos hw ht.1)
    (show w*t < Real.pi by dsimp [w]; nlinarith [mul_pos Real.pi_pos (sub_pos.mpr ht')])
  have hzero : phiD qEight h (coord t) = 0 := by
    rcases mul_eq_zero.mp hprod with HC | HH
    · exact (hC.ne' HC).elim
    · exact (mul_eq_zero.mp HH).resolve_right (mul_pos hw hsin).ne'
  have hy := (strictMonoOn_phiD_large hq qEight_le hh8.le h6.le).injOn
    (hrange t) (hrange t₀) (hzero.trans H₀.symm)
  have ht₀' : t₀ < 1/2 := ht₀.2.trans (by unfold bound; linarith)
  have he := strictMonoOn_coord.injOn ⟨ht.1.le,ht'.le⟩ ⟨ht₀.1.le,ht₀'.le⟩ hy
  simpa only [he] using H

private theorem restrict_to_face {h v : ℝ} (hv : |v| < bound h)
    (H : IsLocalMinOn (chartEnergy h) (chartDomain h) (v,0)) :
    IsLocalMin (packedEnergy8 h) v := by
  let s := {z : ℝ | |z| < bound h}
  have H' := H.comp_continuousOn (g := fun z : ℝ => (z,(0:Release))) (s := s)
    (fun z hz => zero_in_chart hz.le) (continuous_id.prodMk continuous_const).continuousOn hv
  have hs : s ∈ 𝓝 v := (isOpen_lt continuous_abs continuous_const).mem_nhds hv
  simpa only [Function.comp_def,chartEnergy,Release.zero_release_sites,packedEnergy8] using H'.isLocalMin hs

private theorem lift_face_minimum {h₀ : ℝ} (hh : 0 < h₀) (h6 : h₀ < 1/6) :
    ∃ r > (0:ℝ), ∀ h v, |h-h₀| < r → |v| < r → minimizesEnergy 8 h v →
      IsLocalMinOn (chartEnergy h) (chartDomain h) (v,0) := by
  obtain ⟨r,hr,H⟩ := uniform_face_lower hh h6
  refine ⟨r,hr,?_⟩
  intro h v hδ hv hm
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨min (r-|v|) r, lt_min (sub_pos.mpr hv) hr, ?_⟩
  rintro ⟨z,u⟩ ⟨hb,hp⟩
  simp only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,dist_zero_right,max_lt_iff,lt_min_iff] at hb
  have hz : |z| < r := by
    have H₁ : |z| ≤ |z-v|+|v| := by simpa only [sub_add_cancel] using abs_add_le (z-v) v
    linarith [hb.1.1]
  have hu := ((Release.feasible_iff h z u).mp hp).1
  simpa only [chartEnergy,Release.zero_release_sites] using
    (hm.2 z (chart_feasible_packed hp)).trans (H h z u hδ hz hb.2.2 hu)

private theorem center_not_local {h : ℝ} (hc : hcEight < h) (h6 : h < 1/6) :
    ¬IsLocalMinOn (chartEnergy h) (chartDomain h) (0,0) := by
  intro H
  obtain ⟨r,hr,H⟩ := Metric.mem_nhdsWithin_iff.mp H
  obtain ⟨v,u,hv,_,hf,_,hd,_⟩ := centered_saddle_after_critical hc h6 r hr
  have hmem : (v,(0:Release)) ∈ Metric.ball (0,0) r ∩ chartDomain h := by
    refine ⟨?_,hf⟩
    simpa [Metric.mem_ball,Prod.dist_eq,Real.dist_eq] using hv
  have hl := H hmem
  change chartEnergy h (0,0) ≤ chartEnergy h (v,0) at hl
  simp only [chartEnergy,Release.zero_release_sites] at hl hd
  exact hd.not_ge hl

/-- The near-onset part of Proposition 4: the two reflected displacements
are exactly the packed-face global minimizers and the only full-simplex local
minimizers in a fixed neighborhood of the centered cell. Both expansions use
the same physical branch. -/
theorem width_eight_nearby_minimizers :
    ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
      ((fun δ => t δ - Real.sqrt (-6*mixedCritical/fourthCritical)*δ^(1/2:ℝ))
        =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
      ((fun δ => faceEnergy (hcEight+δ) 0 - faceEnergy (hcEight+δ) (t δ) -
        (3*mixedCritical^2/(2*fourthCritical))*δ^2)
          =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
      ((fun δ => -t δ - (-Real.sqrt (-6*mixedCritical/fourthCritical))*δ^(1/2:ℝ))
        =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
      ((fun δ => faceEnergy (hcEight+δ) 0 - faceEnergy (hcEight+δ) (-t δ) -
        (3*mixedCritical^2/(2*fourthCritical))*δ^2)
          =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
      ∃ r > (0:ℝ), ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ t δ < r ∧ t δ < bound (hcEight+δ) ∧
        (∀ v, minimizesEnergy 8 (hcEight+δ) v ↔ v = t δ ∨ v = -t δ) ∧
        ∀ v (u : Release), |v| < r → ‖u‖ < r → (v,u) ∈ chartDomain (hcEight+δ) →
          (IsLocalMinOn (chartEnergy (hcEight+δ)) (chartDomain (hcEight+δ)) (v,u) ↔
            u = 0 ∧ (v = t δ ∨ v = -t δ)) := by
  have hq : 0 < qEight := Real.exp_pos _
  have hcf := (criticalFloor_spec false hq qEight_le).1
  have hp : 0 < hcEight := lt_trans (by norm_num : (0:ℝ)<1/8) hcf.1
  have h6 : hcEight < 1/6 := hcf.2
  obtain ⟨t,ht,hs,hd,hg,_⟩ := widthEight_pitch_laws
  obtain ⟨r₁,hr₁,H₁⟩ := localMin_implies_packed hp h6
  obtain ⟨r₂,hr₂,H₂⟩ := lift_face_minimum hp h6
  have hb : 0 < bound hcEight := by unfold bound; linarith
  let r := min (min r₁ r₂) (bound hcEight/8)
  have hr : 0 < r := lt_min (lt_min hr₁ hr₂) (by positivity)
  have hr₁' : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr₂' : r ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hrb : r ≤ bound hcEight/8 := min_le_right _ _
  refine ⟨t,ht,hd,hg,hd.neg_left.congr_left (fun δ => by ring),
    hg.congr_left (fun δ => by
      rw [show faceEnergy (hcEight+δ) (-t δ) = faceEnergy (hcEight+δ) (t δ)
        from packedEnergy8_even _ _]),r,hr,?_⟩
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have horder : hcEight < criticalFloor true qEight := criticalFloor_order hq qEight_le
  filter_upwards [hpos,hi.eventually_lt_const hr,hs,ht.eventually_lt_const hr,
    hi.eventually_lt_const (sub_pos.mpr horder)] with δ hδ hδr hs htR hδb
  let h := hcEight+δ
  have hgap : |h-hcEight| = δ := by dsimp [h]; rw [add_sub_cancel_left,abs_of_pos hδ]
  have hrh : r < bound h := by
    unfold bound at hrb hb ⊢
    dsimp [h]
    linarith
  have hh : hcEight < h := by dsimp [h]; linarith
  have hh' : h < criticalFloor true qEight := by dsimp [h]; linarith
  have h6' := hh'.trans (criticalFloor_spec true hq qEight_le).1.2
  have hface := stationary_is_face_minimum hh hh' ⟨hs.1,htR.trans hrh⟩ hs.2
  refine ⟨hs.1,htR,htR.trans hrh,hface,?_⟩
  intro v u hv hu hF
  constructor
  · intro HM
    have hu0 := H₁ h v u (by rw [hgap]; exact hδr.trans_le hr₁') (hv.trans_le hr₁') (hu.trans_le hr₁') hF HM
    subst u
    have hm := restrict_to_face (hv.trans hrh) HM
    have hne : v ≠ 0 := by
      rintro rfl
      exact center_not_local hh h6' HM
    have hD : deriv (packedEnergy8 h) |v| = 0 := by
      rcases le_total 0 v with hv' | hv'
      · rw [abs_of_nonneg hv']
        exact hm.deriv_eq_zero
      · rw [abs_of_nonpos hv']
        have H := deriv_comp_neg (f := packedEnergy8 h) (-v)
        rw [show (fun z => packedEnergy8 h (-z)) = packedEnergy8 h from funext (packedEnergy8_even h),
          neg_neg,hm.deriv_eq_zero,neg_zero] at H
        exact H
    have hM := stationary_is_face_minimum hh hh' ⟨abs_pos.mpr hne,hv.trans hrh⟩ hD
    have hval := (hface |v|).mp ((hM |v|).mpr (Or.inl rfl))
    have ha : |v| = t δ := hval.resolve_right (ne_of_gt ((neg_lt_zero.mpr hs.1).trans_le (abs_nonneg v)))
    refine ⟨rfl,?_⟩
    rcases le_total 0 v with H|H
    · exact Or.inl (by simpa [abs_of_nonneg H] using ha)
    · right
      rw [abs_of_nonpos H] at ha
      linarith
  · rintro ⟨rfl,he⟩
    exact H₂ h v (by rw [hgap]; exact hδr.trans_le hr₂') (hv.trans_le hr₂') ((hface v).mpr he)

/-- The nonnegative release chart is a coordinate chart on the full feasible
simplex after pinning the first site. Pulling back a constrained local minimum
therefore preserves and reflects the usual local-minimum predicate on positions. -/
theorem chart_localMin_iff_physical {h : ℝ} {p : ℝ × Release} (hp : p ∈ chartDomain h) :
    IsLocalMinOn (chartEnergy h) (chartDomain h) p ↔
      IsLocalMinOn (physicalEnergy 8 1) {x : Fin 6 → ℝ | x 0 = 0 ∧ Feasible (by decide) h x}
        (Release.sites h p.1 p.2) := by
  let X := fun q : ℝ × Release => Release.sites h q.1 q.2
  let P := fun x : Fin 6 → ℝ => (x 3-1/2,Release.releaseCoordinates h x)
  let S := {x : Fin 6 → ℝ | x 0 = 0 ∧ Feasible (by decide) h x}
  have left (q : ℝ × Release) : P (X q) = q := by
    apply Prod.ext
    · dsimp [P,X,Release.sites]; ring
    · exact Release.releaseCoordinates_sites h _ _
  have right {x : Fin 6 → ℝ} (hx : x ∈ S) : X (P x) = x := Release.reconstruct x hx.1 h
  have hX : Continuous X := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [X,Release.sites] <;> fun_prop
  have hP : Continuous P := by
    apply Continuous.prodMk ((continuous_apply 3).sub continuous_const)
    apply continuous_pi
    intro i
    fin_cases i <;> simp [Release.releaseCoordinates] <;> fun_prop
  have mapsX : MapsTo X (chartDomain h) S := by
    intro q hq
    refine ⟨rfl,?_⟩
    intro i
    simpa only [Release.gaps_eq_gap] using hq i
  have mapsP : MapsTo P S (chartDomain h) := by
    intro x hx i
    change h ≤ Release.gaps (X (P x)) i
    rw [right hx,Release.gaps_eq_gap]
    exact hx.2 i
  have energy (x : Fin 6 → ℝ) : physicalEnergy 8 1 x = imageEnergy 8 x := by
    simpa using physicalEnergy_eq_imageEnergy (N := 6) (by norm_num) 8 1 (by norm_num) (by norm_num) x
  constructor
  · intro H
    have hlocal : IsLocalMinOn (chartEnergy h) (chartDomain h) (P (X p)) := (left p).symm ▸ H
    have hcomp := hlocal.comp_continuousOn (g := P) (s := S) mapsP hP.continuousOn (mapsX hp)
    apply hcomp.congr _ (mapsX hp)
    filter_upwards [self_mem_nhdsWithin] with x hx
    change imageEnergy 8 (X (P x)) = physicalEnergy 8 1 x
    rw [right hx,energy]
  · intro H
    have hcomp := H.comp_continuousOn (g := X) (s := chartDomain h) mapsX hX.continuousOn hp
    apply hcomp.congr _ hp
    exact Eventually.of_forall (fun q => energy (X q))

end GaussianChains.Bifurcation
end

#print axioms GaussianChains.Bifurcation.width_eight_nearby_minimizers
#print axioms GaussianChains.Bifurcation.chart_localMin_iff_physical
