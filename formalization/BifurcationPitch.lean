import BifurcationEmergence
import BifurcationRelease
import PackedFaceModesEnergy

/-! Equation (11) on the original six-particle energy. The floor and
stationarity hypotheses expose precisely the inputs from phase classification. -/

open Filter Asymptotics Set
open scoped Topology
noncomputable section
namespace GaussianChains.Bifurcation

def packedEnergy8 (h t : ℝ) := imageEnergy 8 (PackedFace.sites h t)

theorem packedEnergy8_even (h t : ℝ) : packedEnergy8 h (-t) = packedEnergy8 h t := by
  have h₁ := PackedFace.imageEnergy_difference (s := 8) (by norm_num) h (-t)
  have h₂ := PackedFace.imageEnergy_difference (s := 8) (by norm_num) h t
  rw [PackedFace.coord_neg] at h₁
  unfold packedEnergy8
  linarith only [h₁,h₂]

theorem packedEnergy8_analytic {hc : ℝ} (u : ℝ × ℝ) :
    AnalyticAt ℝ (fun v : ℝ × ℝ => packedEnergy8 (hc+v.1) v.2) u := by
  have hh : AnalyticAt ℝ (fun v : ℝ × ℝ => hc+v.1) u :=
    analyticAt_const.add ((ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _)
  have ht := (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt u
  have hs := Release.sites_analyticAt (U := fun _ _ => (0:ℝ)) hh ht (fun _ => analyticAt_const)
  have ha : AnalyticAt ℝ (fun v : ℝ × ℝ => imageEnergy 8 (Release.sites (hc+v.1) v.2 0)) u :=
    (Release.imageEnergy_analyticAt (s := 8) (by norm_num) _).comp hs
  simpa only [Release.zero_release_sites, packedEnergy8] using ha

/-- The physical branch law at a simple critical floor. The statement uses
the mixed and fourth derivatives of the original cell directly. -/
theorem packedEnergy8_pitchfork {hc A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hcrit : iteratedDeriv 2 (packedEnergy8 hc) 0 = 0)
    (hAf : deriv (fun h => iteratedDeriv 2 (packedEnergy8 h) 0) hc = A)
    (hBf : iteratedDeriv 4 (packedEnergy8 hc) 0 = B)
    (t : ℝ → ℝ) (ht : Tendsto t (𝓝[>] 0) (𝓝 0))
    (hstat : ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ deriv (packedEnergy8 (hc+δ)) (t δ) = 0) :
    ((fun δ => t δ - Real.sqrt (-6*A/B)*δ^(1/2:ℝ))
        =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
    ((fun δ => packedEnergy8 (hc+δ) 0 - packedEnergy8 (hc+δ) (t δ) -
      (3*A^2/(2*B))*δ^2) =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) := by
  let f := fun u : ℝ × ℝ => packedEnergy8 (hc+u.1) u.2
  apply laws_of_even_stationary_branch f packedEnergy8_analytic (fun h v => packedEnergy8_even _ _)
    (by simpa [f,displacementJet] using hcrit) hA hB _ (by simpa [f,displacementJet] using hBf) t ht hstat
  change deriv (fun δ => iteratedDeriv 2 (packedEnergy8 (hc+δ)) 0) 0 = A
  exact (deriv_comp_const_add (fun h => iteratedDeriv 2 (packedEnergy8 h) 0) hc 0).trans
    (by simpa only [add_zero] using hAf)

/-- There is a positive stationary branch of the physical six-site cell
under the critical-derivative tests. Its reflected displacement has the same
physical energy, and the positive stationary displacement is locally unique. -/
theorem packedEnergy8_bifurcation {hc A B : ℝ} (hA : A < 0) (hB : 0 < B)
    (hcrit : iteratedDeriv 2 (packedEnergy8 hc) 0 = 0)
    (hAf : deriv (fun h => iteratedDeriv 2 (packedEnergy8 h) 0) hc = A)
    (hBf : iteratedDeriv 4 (packedEnergy8 hc) 0 = B) :
    ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
      (∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ deriv (packedEnergy8 (hc+δ)) (t δ) = 0) ∧
      ((fun δ => t δ - Real.sqrt (-6*A/B)*δ^(1/2:ℝ)) =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
      ((fun δ => packedEnergy8 (hc+δ) 0 - packedEnergy8 (hc+δ) (t δ) -
        (3*A^2/(2*B))*δ^2) =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
      ∃ r > (0:ℝ), ∀ᶠ δ in 𝓝[>] 0, ∀ u ∈ Ioc 0 r,
        deriv (packedEnergy8 (hc+δ)) u = 0 ↔ u = t δ := by
  let f := fun u : ℝ × ℝ => packedEnergy8 (hc+u.1) u.2
  have han : ∀ u, AnalyticAt ℝ f u := packedEnergy8_analytic
  have heven (h v : ℝ) : f (h,-v) = f (h,v) := packedEnergy8_even _ _
  have hκ : displacementJet f 2 (0,0) = 0 := by simpa [f,displacementJet] using hcrit
  have ha : deriv (fun δ => displacementJet f 2 (δ,0)) 0 = A := by
    change deriv (fun δ => iteratedDeriv 2 (packedEnergy8 (hc+δ)) 0) 0 = A
    exact (deriv_comp_const_add (fun h => iteratedDeriv 2 (packedEnergy8 h) 0) hc 0).trans
      (by simpa only [add_zero] using hAf)
  have hb : displacementJet f 4 (0,0) = B := by simpa [f,displacementJet] using hBf
  obtain ⟨t,ht,hs⟩ := exists_even_stationary_branch f han heven hκ hA hB ha hb
  obtain ⟨hd,hg⟩ := packedEnergy8_pitchfork hA hB hcrit hAf hBf t ht hs
  obtain ⟨r,hr,hu⟩ := nearby_stationary_unique f han heven (hb.symm ▸ hB)
  refine ⟨t,ht,hs,hd,hg,r,hr,?_⟩
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  filter_upwards [hp,hi.eventually_lt_const hr,hs,ht.eventually_lt_const hr]
    with δ hδ hδr hs htr
  intro u hu'
  refine ⟨fun h => hu δ (by rwa [abs_of_pos hδ]) u hu' (t δ) ⟨hs.1,htr.le⟩ h hs.2, ?_⟩
  rintro rfl
  exact hs.2

end GaussianChains.Bifurcation
end
