import ClusterSeriesOrbitsPacked
import ClusterSeriesLocking

namespace GaussianChains.ClusterSeries

open OddBlock

private theorem translate_of_equal_steps (X Y : ℤ → ℝ)
    (hstep : ∀ i, X (i+1)-X i = Y (i+1)-Y i) (i : ℤ) :
    X i = Y i + (X 0 - Y 0) := by
  refine Int.inductionOn' i 0 (by ring) (fun k _ ih => by linarith [hstep k]) ?_
  intro k _ ih
  have ht := hstep (k-1)
  rw [sub_add_cancel] at ht
  linarith

private theorem shift_markedGap (h H : ℝ) (r v a i : ℤ) :
    markedGap h H (r+v) v a i = markedGap h H (r+v) r a (i+r) := by
  have e : a+v+r ≡ a [ZMOD r+v] := by
    rw [show a+v+r=a+(r+v) by ring]
    exact Int.add_modEq_right
  have hm₁ : (i+r ≡ a [ZMOD r+v]) ↔ (i ≡ a+v [ZMOD r+v]) :=
    ⟨fun hi => (hi.trans e.symm).add_right_cancel' r, fun hi => (hi.add_right r).trans e⟩
  have hm₂ : (i+r ≡ a+r [ZMOD r+v]) ↔ (i ≡ a [ZMOD r+v]) :=
    ⟨Int.ModEq.add_right_cancel' _, fun hi => hi.add_right _⟩
  simp only [markedGap, hm₁, hm₂, or_comm]

/-- Swapping the two odd blocks translates the physical chain by half a
period and moves the cut by the full odd length of the first block. -/
theorem packedSites_swap_lift (k l : ℕ) (h : ℝ) (i : ℤ) :
    integerSite (by omega) (packedSites l k h) i =
      integerSite (by omega) (packedSites k l h) (i + (2*(k:ℤ)+1)) - 1/2 := by
  let Y := integerSite (by omega) (packedSites l k h)
  let X := integerSite (by omega) (packedSites k l h)
  let r := 2*(k:ℤ)+1
  let v := 2*(l:ℤ)+1
  have hsteps (j : ℤ) : Y (j+1)-Y j = X (j+1+r) - X (j+r) := by
    rw [show j+1+r=j+r+1 by ring]
    simp only [Y, X, integerSite_step, packedSites_marked]
    rw [add_comm (2*(l:ℤ)+1), add_comm (l:ℝ) (k:ℝ)]
    exact shift_markedGap _ _ r v (-1) j
  have hdiff := translate_of_equal_steps Y (fun j => X (j+r)) hsteps i
  have hy : Y 0 = -(l:ℝ)*h := by
    change integerSite _ _ ((0 : Fin ((2*l+1)+(2*k+1))).val:ℤ) = _
    rw [integerSite_fin, packedSites_eq]
    simp
  have hx : X r = 1/2 - (l:ℝ)*h := by
    let j : Fin ((2*k+1)+(2*l+1)) := ⟨2*k+1,by omega⟩
    have hj : (j.val:ℤ) = r := rfl
    change integerSite _ _ r = _
    rw [← hj, integerSite_fin, packedSites_eq]
    simp [j]
    ring
  simp only [zero_add,hy,hx] at hdiff
  change Y i = X (i+r)-1/2
  linarith

private theorem integerSite_add_cycles {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (i z : ℤ) :
    integerSite hN x (i+N*z) = integerSite hN x i + (z:ℝ) := by
  refine Int.inductionOn' z 0 (by simp) ?_ ?_
  · intro k _ ih
    rw [show i+(N:ℤ)*(k+1)=(i+N*k)+N by ring, integerSite_add_period, ih]
    push_cast
    ring
  · intro k _ ih
    have ht := integerSite_add_period hN x (i+N*(k-1))
    rw [show i+(N:ℤ)*(k-1)+N=i+N*k by ring, ih] at ht
    push_cast
    linarith

/-- A finite equality of recut ordered coordinates extends to every label
in the full chain, including negative periods. -/
theorem integerSite_recut_eq {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (e : N=M) (x : Fin N → ℝ) (y : Fin M → ℝ) (t : Fin N) (c : ℝ)
    (heq : ∀ i, shiftLifts hN x t i = y (Fin.cast e i) + c) (i : ℤ) :
    integerSite hN x (i + (t.val:ℤ)) = integerSite hM y i + c := by
  subst M
  let j := cellIndex hN i
  let z := i/(N:ℤ)
  have hj : (j.val:ℤ) = i%(N:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne' : (N:ℤ)≠0))
  have hi : (j.val:ℤ) + N*z = i := by
    rw [hj]
    exact Int.emod_add_mul_ediv i N
  have ht : integerSite hN x ((j.val:ℤ) + t.val) = y j + c := heq j
  have hh : i + (t.val:ℤ) = ((j.val:ℤ)+t.val) + N*z := by linarith
  rw [hh, integerSite_add_cycles, ht, ← hi, integerSite_add_cycles, integerSite_fin]
  ring

/-- Both orders of a balanced split, and every choice of finite cut in
`IsBalancedPacked`, lie among the actual translated recuts of one prescribed
ordered split. Together with `packed_sites_orbits_iff` this transfers the
orbit count from the canonical coordinates to the entire locked family. -/
theorem balancedPacked_is_recut {m : ℕ} {hm : 0<2*m} {h : ℝ} {x : Fin (2*m) → ℝ}
    (hx : IsBalancedPacked hm h x)
    (k l : ℕ) (hcount : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1) :
    ∃ t : ℤ, ∃ c : ℝ, ∀ i, integerSite hm x i =
      integerSite (by omega) (packedSites k l h) (i+t) + c := by
  obtain ⟨u,v,e,hu,hv,t,c,heq⟩ := hx
  have hrec (i : ℤ) := integerSite_recut_eq hm (by omega) e x (packedSites u v h)
    t c heq (i-t.val)
  have hs : (u=k ∧ v=l) ∨ (u=l ∧ v=k) := by omega
  rcases hs with ⟨hu',hv'⟩ | ⟨hu',hv'⟩
  · subst u
    subst v
    refine ⟨-(t.val:ℤ),c,fun i => ?_⟩
    simpa [sub_eq_add_neg] using hrec i
  · subst u
    subst v
    refine ⟨2*(k:ℤ)+1-t.val, c-1/2, fun i => ?_⟩
    have ht := hrec i
    rw [sub_add_cancel, packedSites_swap_lift] at ht
    rw [show i+(2*(k:ℤ)+1-t.val)=i-t.val+(2*k+1) by ring]
    linarith

private theorem sameSpecies_of_translations {X X' Y Y' : ℤ → ℝ} {c d : ℝ}
    (hx : ∀ i, X i = X' i + c) (hy : ∀ i, Y i = Y' i + d) :
    SameSpeciesSites X Y ↔ SameSpeciesSites X' Y' := by
  rw [sameSpeciesSites_iff_steps, sameSpeciesSites_iff_steps]
  simp only [hx,hy,add_sub_add_right_eq_sub]

theorem sameSpecies_packed_orders_iff (k l : ℕ) {h : ℝ}
    (hh : h < 1/(((2*k+1)+(2*l+1):ℕ):ℝ)) :
    SameSpeciesSites (integerSite (by omega) (packedSites k l h))
      (integerSite (by omega) (packedSites l k h)) ↔ k=l := by
  let X := integerSite (by omega) (packedSites k l h)
  let Y := integerSite (by omega) (packedSites l k h)
  let r := 2*(k:ℤ)+1
  have hx (i : ℤ) : X i = X (i+0)+0 := by simp
  have hy (i : ℤ) : Y i = X (i+r) + (-(1/2 : ℝ)) := packedSites_swap_lift k l h i
  change SameSpeciesSites X Y ↔ k=l
  exact (sameSpecies_of_translations hx hy).trans
    ((packed_sites_orbits_iff k l hh 0 r).trans (by dsimp only [r]; omega))

/-- The classification applies to every pair in the finite physical
normal form, regardless of which of the two arrangements its witness chose. -/
theorem balancedPacked_pair_orbits {m : ℕ} {hm : 0<2*m} {h : ℝ}
    (k l : ℕ) (hcount : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1)
    (hh : h < 1/(((2*k+1)+(2*l+1):ℕ):ℝ)) (x y : Fin (2*m) → ℝ)
    (hx : IsBalancedPacked hm h x) (hy : IsBalancedPacked hm h y) :
    let P := integerSite (by omega) (packedSites k l h)
    ∃ t u : ℤ, ∃ c d : ℝ, (∀ i, integerSite hm x i = P (i+t)+c) ∧
      (∀ i, integerSite hm y i = P (i+u)+d) ∧
      (SameSpeciesSites (integerSite hm x) (integerSite hm y) ↔ t%2=u%2 ∨ k=l) := by
  obtain ⟨t,c,ht⟩ := balancedPacked_is_recut hx k l hcount hkl hlk
  obtain ⟨u,d,hu⟩ := balancedPacked_is_recut hy k l hcount hkl hlk
  exact ⟨t,u,c,d,ht,hu,(sameSpecies_of_translations ht hu).trans (packed_sites_orbits_iff k l hh t u)⟩

/-- The two orders both occur in the labelled finite configuration space. -/
theorem balancedPacked_of_canonical {m : ℕ} (hm : 0<2*m) (h : ℝ) (k l : ℕ)
    (e : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1) :
    IsBalancedPacked hm h (fun i => packedSites k l h (Fin.cast e i)) := by
  refine ⟨k,l,e,hkl,hlk,⟨0,hm⟩,0,fun i => ?_⟩
  simpa only [shiftLifts, Fin.val_mk, Nat.add_zero, add_zero] using
    liftSite_fin hm (fun j => packedSites k l h (Fin.cast e j)) i

/-- Concrete representatives of all species-preserving isometry classes
of the balanced packed family. The two representatives are equivalent
exactly when the odd blocks have the same cardinality. -/
theorem balancedPacked_representatives {m : ℕ} {hm : 0<2*m} {h : ℝ}
    (k l : ℕ) (hcount : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1)
    (hh : h < 1/(((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let P := integerSite (by omega) (packedSites k l h)
    let Q := integerSite (by omega) (packedSites l k h)
    (SameSpeciesSites P Q ↔ k=l) ∧ ∀ x : Fin (2*m) → ℝ, IsBalancedPacked hm h x →
      SameSpeciesSites (integerSite hm x) P ∨ SameSpeciesSites (integerSite hm x) Q := by
  let P := integerSite (by omega) (packedSites k l h)
  let Q := integerSite (by omega) (packedSites l k h)
  let r := 2*(k:ℤ)+1
  refine ⟨sameSpecies_packed_orders_iff k l hh, ?_⟩
  intro x hx
  obtain ⟨t,c,ht⟩ := balancedPacked_is_recut hx k l hcount hkl hlk
  have hp (i : ℤ) : P i = P (i+0)+0 := by simp
  have hq (i : ℤ) : Q i = P (i+r)+(-(1/2:ℝ)) := packedSites_swap_lift k l h i
  rcases (show t%2=0 ∨ t%2=1 by omega) with he | ho
  · exact Or.inl ((sameSpecies_of_translations ht hp).mpr
      ((packed_sites_orbits_iff k l hh t 0).mpr (.inl (by omega))))
  · exact Or.inr ((sameSpecies_of_translations ht hq).mpr
      ((packed_sites_orbits_iff k l hh t r).mpr (.inl (by dsimp only [r]; omega))))

#print axioms balancedPacked_is_recut
#print axioms balancedPacked_pair_orbits
#print axioms balancedPacked_representatives

end GaussianChains.ClusterSeries
