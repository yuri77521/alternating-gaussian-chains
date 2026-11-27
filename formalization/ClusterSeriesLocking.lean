import ClusterSeriesCandidate
import ChainSymmetry

namespace GaussianChains.ClusterSeries

open Real
open Filter Topology
open scoped Asymptotics

/-- The normal form in Theorem 1, with the labeled species at index zero fixed.
Either block is allowed at the chosen cyclic cut. -/
def IsBalancedPacked {m : ℕ} (hm : 0 < 2*m) (h : ℝ) (x : Fin (2*m) → ℝ) : Prop :=
  ∃ (k l : ℕ) (e : 2*m = (2*k+1)+(2*l+1)),
    k ≤ l+1 ∧ l ≤ k+1 ∧ ∃ (t : Fin (2*m)) (c : ℝ),
    ∀ i, shiftLifts hm x t i = packedSites k l h (Fin.cast e i) + c

private theorem energy_cast {M N : ℕ} (e : M = N) (s : ℝ) (y : Fin N → ℝ) :
    imageEnergy s (fun i => y (Fin.cast e i)) = imageEnergy s y := by subst N; rfl

private theorem gap_cast_translate {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (e : M = N) (c : ℝ) (y : Fin N → ℝ) (i : Fin M) :
    gap hM (fun i => y (Fin.cast e i) + c) i = gap hN y (Fin.cast e i) := by
  subst N
  simp only [gap,liftSite,Fin.cast_refl,id_eq]
  ring

theorem balancedPacked_feasible {m : ℕ} {hm : 0 < 2*m} {h : ℝ} {x : Fin (2*m) → ℝ}
    (hh : h ≤ 1 / ((2*m:ℕ):ℝ)) (hx : IsBalancedPacked hm h x) : Feasible hm h x := by
  letI : NeZero (2*m) := ⟨hm.ne'⟩
  obtain ⟨k,l,e,_,_,t,c,hr⟩ := hx
  apply (feasible_shiftLifts_iff hm h x t).mp
  rw [funext hr]
  intro i
  rw [gap_cast_translate hm (by omega : 0 < (2*k+1)+(2*l+1))]
  exact packedSites_feasible k l h (e ▸ hh) _

theorem balancedPacked_energy {m : ℕ} {hm : 0 < 2*m} {h : ℝ} {x : Fin (2*m) → ℝ}
    (hx : IsBalancedPacked hm h x) (s : ℝ) :
    ∃ k l : ℕ, 2*m = (2*k+1)+(2*l+1) ∧ k ≤ l+1 ∧ l ≤ k+1 ∧
      imageEnergy s x = imageEnergy s (packedSites k l h) := by
  letI : NeZero (2*m) := ⟨hm.ne'⟩
  obtain ⟨k,l,e,hk,hl,t,c,hr⟩ := hx
  refine ⟨k,l,e,hk,hl,?_⟩
  rw [← imageEnergy_shiftLifts hm (dvd_mul_right ..) s x t, funext hr, imageEnergy_translate,
    energy_cast]

private theorem same_balanced_energy {m k l i j : ℕ} {s : ℝ} (hs : 0 < s) (h : ℝ)
    (hk : 2*m=(2*k+1)+(2*l+1)) (hkl : k ≤ l+1) (hlk : l ≤ k+1)
    (hi : 2*m=(2*i+1)+(2*j+1)) (hij : i ≤ j+1) (hji : j ≤ i+1) :
    imageEnergy s (packedSites k l h) = imageEnergy s (packedSites i j h) := by
  have H : (k=i ∧ l=j) ∨ (k=j ∧ l=i) := by omega
  rcases H with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact imageEnergy_swap_blocks _ _ hs h

/-- Compact attainment and the equality of both ordered balanced splits turn
the necessary normal form into a classification of every global minimizer. -/
theorem groundState_iff_of_locking {m : ℕ} (hm : 0 < 2*m) {h s : ℝ}
    (hs : 0<s) (h₀ : 0≤h) (h₁ : h≤1/((2*m:ℕ):ℝ))
    (lock : ∀ x, IsGroundState hm h s x → IsBalancedPacked hm h x)
    (x : Fin (2*m) → ℝ) : IsGroundState hm h s x ↔ IsBalancedPacked hm h x := by
  refine ⟨lock x, ?_⟩
  intro hp
  obtain ⟨y, hy⟩ := exists_groundState hm h₀ h₁ hs
  obtain ⟨i,j,he,hi,hj,hy'⟩ := balancedPacked_energy (lock y hy) s
  obtain ⟨k,l,he',hk,hl,hx'⟩ := balancedPacked_energy hp s
  refine ⟨balancedPacked_feasible h₁ hp, fun z hz => ?_⟩
  rw [hx', same_balanced_energy hs h he' hk hl he hi hj, ← hy']
  exact hy.2 z hz

/-- Once every minimum has the classified form, either prescribed balanced
ordered split gives Eq. (6) for the original minimum energy. -/
theorem minimumEnergy_eq_of_locking {m : ℕ} (hm : 0 < 2*m) {h s : ℝ}
    (hs : 0<s) (h₀ : 0≤h) (h₁ : h≤1/((2*m:ℕ):ℝ))
    (lock : ∀ x, IsGroundState hm h s x → IsBalancedPacked hm h x)
    (k l : ℕ) (he : 2*m=(2*k+1)+(2*l+1)) (hk : k≤l+1) (hl : l≤k+1) :
    minimumEnergy hm h s = 1 - 2*sqrt (π/s)/((2*m:ℕ):ℝ) *
      packedMass k l (exp (-(π^2)/s)) (2*π*h) := by
  obtain ⟨y, hy⟩ := exists_groundState hm h₀ h₁ hs
  obtain ⟨i,j,he',hi,hj,hy'⟩ := balancedPacked_energy (lock y hy) s
  rw [← groundState_energy_eq_minimum hy, hy', same_balanced_energy hs h he' hi hj he hk hl,
    imageEnergy_packedSites k l hs, he]

/-- The fourth-order minimum expansion follows from the necessary locking
classification on any punctured interval of positive angular floors. -/
theorem minimumEnergy_fourth_of_locking {m : ℕ} (hm : 0 < 2*m) {s : ℝ}
    (hs : 0<s) (k l : ℕ) (he : 2*m=(2*k+1)+(2*l+1)) (hk : k≤l+1) (hl : l≤k+1)
    (lock : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ x, IsGroundState hm (η/(2*π)) s x →
      IsBalancedPacked hm (η/(2*π)) x) :
    (fun η : ℝ => minimumEnergy hm (η/(2*π)) s - energyPoly k l (2*m) s η)
      =O[𝓝[>] 0] (fun η : ℝ => η^6) := by
  apply ((packedEnergy_fourth_dipole k l (2*m) hs).mono nhdsWithin_le_nhds).congr' ?_
    Filter.EventuallyEq.rfl
  have hN : (0:ℝ) < ((2*m:ℕ):ℝ) := by exact_mod_cast hm
  have hband : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1/((2*m:ℕ):ℝ)*(2*π) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [lock,hband,self_mem_nhdsWithin] with η hloc hη hp
  have hh : 0 ≤ η/(2*π) := div_nonneg (le_of_lt hp) (by positivity)
  have heq := minimumEnergy_eq_of_locking hm hs hh ((div_le_iff₀ (by positivity)).mpr
    hη.le) hloc k l he hk hl
  have H : 2*π*(η/(2*π)) = η := by field_simp
  simp only [H] at heq
  rw [heq]

end GaussianChains.ClusterSeries

