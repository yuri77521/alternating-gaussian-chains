import ClustersWidthPhysical
import ClustersContactPath
import ClustersSelectionGeometry
import ChainMinimum
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A one-gap contraction remains feasible on the full cyclic cell.
All angular gaps are compared to 2πh. A strict positive derivative is
incompatible with a ground state when the contracted gap is slack. -/
noncomputable section
namespace GaussianChains.Clusters
open Real Set Filter Topology OddBlock

theorem joined_left_contraction {k l p : ℕ} {u v : ℕ → ℝ} {h t : ℝ}
    (hx : Feasible (by omega) h (joinedSites k l u v)) (hp : 0 < p) (hp' : p ≤ 2*k)
    (ht : t ≤ 0) (hg : 2*π*h ≤ u p-u (p-1)+t) :
    Feasible (by omega) h (joinedSites k l (varyGap u p t) v) := by
  obtain ⟨hu,hv,hcross,hwrap⟩ := (joinedBlocks_feasible_iff _ _ _ _ _).1 hx
  obtain ⟨hfirst,hlast⟩ := varied_endpoints u hp hp' ht
  exact (joinedBlocks_feasible_iff _ _ _ _ _).2
    ⟨varied_feasible u hu hg, hv, by linarith, by linarith⟩

theorem joined_right_contraction {k l p : ℕ} {u v : ℕ → ℝ} {h t : ℝ}
    (hx : Feasible (by omega) h (joinedSites k l u v)) (hp : 0 < p) (hp' : p ≤ 2*l)
    (ht : t ≤ 0) (hg : 2*π*h ≤ v p-v (p-1)+t) :
    Feasible (by omega) h (joinedSites k l u (varyGap v p t)) := by
  obtain ⟨hu,hv,hcross,hwrap⟩ := (joinedBlocks_feasible_iff _ _ _ _ _).1 hx
  obtain ⟨hfirst,hlast⟩ := varied_endpoints v hp hp' ht
  exact (joinedBlocks_feasible_iff _ _ _ _ _).2
    ⟨hu, varied_feasible v hv hg, by linarith, by linarith⟩

private theorem left_min_slope_nonpos {f : ℝ → ℝ} {d ε : ℝ} (hε : 0 < ε)
    (hm : ∀ t ∈ Icc (-ε) 0, f 0 ≤ f t) (hd : HasDerivAt f d 0) : d ≤ 0 := by
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  have near : ∀ᶠ t : ℝ in 𝓝[<] 0, -ε < t :=
    (eventually_gt_nhds (neg_neg_of_pos hε)).filter_mono nhdsWithin_le_nhds
  filter_upwards [near, self_mem_nhdsWithin (s := Iio (0:ℝ))] with t ht ht0
  rw [slope_def_field, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm t ⟨ht.le, ht0.le⟩)) ht0.le

/-- A positive derivative rules out slack whenever the full cyclic path can
lower the chosen gap down to its floor. A positive affine normalization
of the physical energy is allowed, as in the paper's deficit F. -/
theorem groundState_active_gap {N : ℕ} {hN : 0 < N} {h s g η d : ℝ}
    (X : ℝ → Fin N → ℝ) (F : (Fin N → ℝ) → ℝ) (hx : IsGroundState hN h s (X 0))
    (hg : η ≤ g) (hf : ∀ t : ℝ, t ≤ 0 → η ≤ g+t → Feasible hN h (X t))
    (horder : ∀ y, imageEnergy s (X 0) ≤ imageEnergy s y → F (X 0) ≤ F y)
    (hd : HasDerivAt (fun t => F (X t)) d 0) (hpos : 0 < d) : g = η := by
  apply le_antisymm _ hg
  by_contra! hslack
  have hε : 0 < g-η := sub_pos.mpr hslack
  have H := left_min_slope_nonpos hε (f := fun t => F (X t))
    (fun t ht => horder _ (hx.2 (X t) (hf t ht.2 (by linarith [ht.1])))) hd
  exact hpos.not_ge H

private theorem varyGap_zero (u : ℕ → ℝ) (p : ℕ) : varyGap u p 0 = u := by
  funext i
  simp [varyGap]

private theorem angularDeficit_mono {N : ℕ} (he : ∃ m, N = 2*m) {s : ℝ} (hs : 0 < s)
    (b : ℝ) (x y : Fin N → ℝ) (hxy : imageEnergy s x ≤ imageEnergy s y) :
    b - angularScore (exp (-(π^2)/s)) x ≤ b - angularScore (exp (-(π^2)/s)) y := by
  obtain ⟨m, rfl⟩ := he
  by_cases hm : m = 0
  · subst m
    have hxy : x = y := funext fun i => Fin.elim0 i
    rw [hxy]
  · rw [imageEnergy_eq_angularScore m hs, imageEnergy_eq_angularScore m hs] at hxy
    have hc : 0 < 2*sqrt (π/s)*exp (-(π^2)/s)/((2*m:ℕ):ℝ) := by
      have hm' : 0 < m := Nat.pos_of_ne_zero hm
      positivity
    rw [sub_le_sub_iff_left, mul_le_mul_iff_right₀ hc] at hxy
    exact sub_le_sub_left hxy b

theorem groundState_left_gap_tight {k l p : ℕ} {u v : ℕ → ℝ} {h s d b : ℝ} (hs : 0 < s)
    (hx : IsGroundState (by omega) h s (joinedSites k l u v))
    (hp : 0 < p) (hp' : p ≤ 2*k)
    (hd : HasDerivAt (fun t => b - angularScore (exp (-(π^2)/s)) (joinedSites k l (varyGap u p t) v)) d 0)
    (hpos : 0 < d) : u p-u (p-1) = 2*π*h := by
  apply groundState_active_gap (fun t => joinedSites k l (varyGap u p t) v)
    (fun z => b - angularScore (exp (-(π^2)/s)) z)
    (by simpa only [varyGap_zero] using hx) _ _
    (angularDeficit_mono ⟨k+l+1, by omega⟩ hs b _) hd hpos
  · have hu := ((joinedBlocks_feasible_iff _ _ _ _ _).1 hx.1).1 (p-1) (by omega)
    simpa only [Nat.sub_add_cancel hp] using hu
  · exact fun t ht hg => joined_left_contraction hx.1 hp hp' ht hg

theorem groundState_right_gap_tight {k l p : ℕ} {u v : ℕ → ℝ} {h s d b : ℝ} (hs : 0 < s)
    (hx : IsGroundState (by omega) h s (joinedSites k l u v))
    (hp : 0 < p) (hp' : p ≤ 2*l)
    (hd : HasDerivAt (fun t => b - angularScore (exp (-(π^2)/s)) (joinedSites k l u (varyGap v p t))) d 0)
    (hpos : 0 < d) : v p-v (p-1) = 2*π*h := by
  apply groundState_active_gap (fun t => joinedSites k l u (varyGap v p t))
    (fun z => b - angularScore (exp (-(π^2)/s)) z)
    (by simpa only [varyGap_zero] using hx) _ _
    (angularDeficit_mono ⟨k+l+1, by omega⟩ hs b _) hd hpos
  · have hv := ((joinedBlocks_feasible_iff _ _ _ _ _).1 hx.1).2.1 (p-1) (by omega)
    simpa only [Nat.sub_add_cancel hp] using hv
  · exact fun t ht hg => joined_right_contraction hx.1 hp hp' ht hg

#print axioms groundState_left_gap_tight
#print axioms groundState_right_gap_tight

end GaussianChains.Clusters
