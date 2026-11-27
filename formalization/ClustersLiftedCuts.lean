import ClustersOddSplit
import ClustersLocalizationRegions

/-! Lift the two opposite middle cuts to an ordered pair in one full turn,
retaining the original labels across the periodic boundary. -/
noncomputable section
namespace GaussianChains.Occupation
open Real Set

private theorem lift_rank {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {c : ℝ}
    (hc : c ≤ angle hN x 0 + 2*π) :
    ∃ p ≤ 2*m, ∀ i : ℕ, angle hN x i < c ↔ i < p := by
  obtain ⟨p,hp,hi⟩ := exists_cut _ (angle_monotone hx) c (2*m)
  refine ⟨p,hp,fun i ↦ ?_⟩
  by_cases h : i < 2*m
  · exact hi i h
  · have he : c ≤ angle hN x (0+2*m) := by rwa [angle_period]
    exact iff_of_false (not_lt.mpr (he.trans (angle_monotone hx (by omega)))) (by omega)

private theorem lift_rank_period {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {c : ℝ} (hc : angle hN x 0 < c)
    {p : ℕ} (hp : ∀ i, angle hN x i < c ↔ i < p) (i : ℕ) :
    angle hN x i < c + 2*π ↔ i < p+2*m := by
  by_cases hi : i < 2*m
  · have he : angle hN x i ≤ angle hN x (0+2*m) := angle_monotone hx (by omega)
    rw [angle_period] at he
    exact iff_of_true (by linarith) (by omega)
  · obtain ⟨j,rfl⟩ : ∃ j, i = j+2*m := ⟨i-2*m, by omega⟩
    rw [angle_period, add_lt_add_iff_right, add_lt_add_iff_right, hp]

private theorem rank_mono {θ : ℕ → ℝ} {a b : ℝ} {p q : ℕ}
    (hp : ∀ i, θ i < a ↔ i<p) (hq : ∀ i, θ i < b ↔ i<q) (hab : a≤b) : p≤q := by
  by_contra! h
  exact (lt_irrefl q) ((hq q).mp (((hp q).mpr h).trans_le hab))

/-- An odd cut rank starts strictly before the end of the displayed period.
The two odd lengths exhaust the period even when the unoccupied cut is in
the next display. Every lifted site is assigned to its own antipodal center. -/
theorem lifted_cuts {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {y z ρ : ℝ}
    (hy : y ∈ Icc (π/4) (3*π/4)) (hz : z ∈ Icc (5*π/4) (7*π/4))
    (hyo : y ∈ circleSet hN x) (hzo : z ∉ circleSet hN x)
    (hr : ρ < π/4)
    (hloc : ∀ i : Fin (2*m), ∃ k : ℤ, |2*π*x i - (k:ℝ)*π| ≤ ρ) :
    ∃ p k l : ℕ, ∃ phase : ℝ, p < 2*m ∧ (2*k+1)+(2*l+1)=2*m ∧
      (∀ i < 2*k+1, |angle hN x (p+i) - phase| ≤ ρ) ∧
      (∀ j < 2*l+1, |angle hN x (p+(2*k+1)+j) - (phase+π)| ≤ ρ) := by
  let A := cutRepresentative hN x y
  let B := A+(z-y)
  let t₀ := angle hN x 0
  let d : ℤ := toIocDiv (show 0 < 2*π by positivity) t₀ y
  have ha : A ∈ Ioc t₀ (t₀+2*π) := toIocMod_mem_Ioc _ _ _
  have hy' : A+(d:ℝ)*(2*π) = y := by
    simpa only [A, d, t₀, cutRepresentative, zsmul_eq_mul] using
      toIocMod_add_toIocDiv_zsmul (show 0 < 2*π by positivity) t₀ y
  have hz' : B+(d:ℝ)*(2*π) = z := by dsimp [B]; linarith only [hy']
  have hAB : A < B := by dsimp [B]; linarith only [hy.2,hz.1,pi_pos]
  have hBA : B < A+2*π := by dsimp [B]; linarith only [hy.1,hz.2,pi_pos]
  obtain ⟨p,hp,Hp⟩ := lift_rank hx ha.2
  have hpo : p%2 = 1 := (inCell_iff_cut_odd hp (fun i _ => Hp i)).mp
    ((mem_inCell_cutRepresentative hx y).mpr hyo)
  have hq : ∃ q : ℕ, q%2=0 ∧ ∀ i, angle hN x i < B ↔ i<q := by
    by_cases H : B ≤ t₀+2*π
    · obtain ⟨q,hq,Hq⟩ := lift_rank hx H
      have hn : B ∉ inCell hN x := by
        intro hb
        exact hzo (mem_circleSet_iff.mpr ⟨d, by rwa [show z-(d:ℝ)*(2*π)=B by linarith only [hz']]⟩)
      have hq' := (inCell_iff_cut_odd hq (fun i _ => Hq i)).not.mp hn
      exact ⟨q,by omega,Hq⟩
    · let b := B-2*π
      have hb₀ : t₀ < b := by dsimp [b]; linarith
      have hb₁ : b ≤ t₀+2*π := by dsimp [b]; linarith only [hBA,ha.2]
      obtain ⟨r,hr',Hr⟩ := lift_rank hx hb₁
      have hn : b ∉ inCell hN x := by
        intro hb
        apply hzo
        refine mem_circleSet_iff.mpr ⟨d+1,?_⟩
        have he : z-((d+1:ℤ):ℝ)*(2*π)=b := by
          push_cast; dsimp [b]; linarith only [hz']
        rwa [he]
      have heven := (inCell_iff_cut_odd hr' (fun i _ => Hr i)).not.mp hn
      refine ⟨r+2*m,by omega,fun i => ?_⟩
      simpa only [b,sub_add_cancel] using lift_rank_period hx hb₀ Hr i
  obtain ⟨q,hqe,Hq⟩ := hq
  have HP := lift_rank_period hx ha.1 Hp
  have hpq := rank_mono Hp Hq hAB.le
  have hqp := rank_mono Hq HP hBA.le
  let k := (q-p)/2
  let l := (p+2*m-q)/2
  have hlen : 2*k+1 = q-p := by dsimp [k]; omega
  have hlen' : 2*l+1 = p+2*m-q := by dsimp [l]; omega
  have near (n : ℕ) : ∃ j : ℤ, |angle hN x n - (A-y) - (j:ℝ)*π| ≤ ρ := by
    obtain ⟨u,hu⟩ := hloc ⟨n%(2*m), Nat.mod_lt _ hN⟩
    refine ⟨u+2*(((n/(2*m):ℕ):ℤ)+d),?_⟩
    have eq : angle hN x n - (A-y) - ((u+2*(((n/(2*m):ℕ):ℤ)+d):ℤ):ℝ)*π =
        2*π*x ⟨n%(2*m),Nat.mod_lt _ hN⟩ -(u:ℝ)*π := by
      have algebra (v : ℝ) (b : ℕ) :
          2*π*(v+(b:ℝ)) - (A-y) - ((u+2*((b:ℤ)+d):ℤ):ℝ)*π = 2*π*v-(u:ℝ)*π := by
        push_cast
        linarith only [hy']
      exact algebra _ _
    rwa [eq]
  refine ⟨p,k,l,A-y+π,by omega,by omega,?_,?_⟩
  · intro i hi
    let n := p+i
    have hl₀ : A ≤ angle hN x n := not_lt.mp ((Hp n).not.mpr (by dsimp [n]; omega))
    have hl₁ : angle hN x n < B := (Hq n).mpr (by dsimp [n]; omega)
    have ha' := (Localization.endpoint_of_arc hy.1 hy.2 hz.1 hz.2
      (show y ≤ angle hN x n-(A-y) by linarith only [hl₀])
      (show angle hN x n-(A-y) ≤ y+2*π by linarith only [hl₁,hBA])
      hr (near n)).1 (by dsimp [B] at hl₁; linarith only [hl₁])
    convert ha' using 2 <;> ring
  · intro j hj
    let n := p+(2*k+1)+j
    have hl₀ : B ≤ angle hN x n := not_lt.mp ((Hq n).not.mpr (by dsimp [n]; omega))
    have hl₁ : angle hN x n < A+2*π := (HP n).mpr (by dsimp [n]; omega)
    have ha' := (Localization.endpoint_of_arc hy.1 hy.2 hz.1 hz.2
      (show y ≤ angle hN x n-(A-y) by linarith only [hl₀,hAB])
      (show angle hN x n-(A-y) ≤ y+2*π by linarith only [hl₁])
      hr (near n)).2 (by dsimp [B] at hl₀; linarith only [hl₀])
    convert ha' using 2 <;> ring

end GaussianChains.Occupation

