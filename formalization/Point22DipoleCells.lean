import Point22SixScore
import Point22Packed
import ChainSymmetry
import Point22Physical

/-! Removing two disjoint contacting pairs. After cutting at a residual site
there are just two cases: both dipoles lie on the same arc, or one on each arc.
No maximality or separation of the contacts from other contacts is assumed. -/

namespace GaussianChains.Point22

open Set
noncomputable section

def sameArcCell (h r u v : ℝ) : Fin 6 → ℝ := ![0,u,u+h,v,v+h,r]
def splitArcCell (h r u v : ℝ) : Fin 6 → ℝ := ![0,u,u+h,r,r+v,r+v+h]

def interaction (G : ℝ → ℝ) (h arc u : ℝ) :=
  G (u+h) - G u + (G (arc-u) - G (arc-(u+h)))

set_option maxHeartbeats 1500000 in
theorem sameArc_score (s h r u v : ℝ) :
    pairScore s (sameArcCell h r u v) =
      -kernel s r - 2*kernel s h +
      interaction (kernel s) h r u + interaction (kernel s) h r v -
      centeredDifference (kernel s) h (v-u) := by
  rw [six_score_terms]
  generalize kernel s = G
  simp only [show sameArcCell h r u v 0 = 0 from rfl,
    show sameArcCell h r u v 1 = u from rfl,show sameArcCell h r u v 2 = u+h from rfl,
    show sameArcCell h r u v 3 = v from rfl,show sameArcCell h r u v 4 = v+h from rfl,
    show sameArcCell h r u v 5 = r from rfl, interaction, centeredDifference]
  ring_nf

set_option maxHeartbeats 1500000 in
theorem splitArc_score (s h r u v : ℝ) :
    pairScore s (splitArcCell h r u v) =
      -kernel s r - 2*kernel s h +
      interaction (kernel s) h r u + interaction (kernel s) h (1-r) v +
      centeredDifference (kernel s) h (r+v-u) := by
  have reflect (d : ℝ) : kernel s (1-d) = kernel s d := by
    rw [show 1-d = -d+(1:ℤ) by push_cast; ring, kernel_add_int, kernel_neg]
  rw [six_score_terms]
  simp only [show splitArcCell h r u v 0 = 0 from rfl,
    show splitArcCell h r u v 1 = u from rfl,show splitArcCell h r u v 2 = u+h from rfl,
    show splitArcCell h r u v 3 = r from rfl,show splitArcCell h r u v 4 = r+v from rfl,
    show splitArcCell h r u v 5 = r+v+h from rfl, interaction, centeredDifference]
  rw [show 1-r-v = 1-(r+v) by ring, show 1-r-(v+h) = 1-(r+v+h) by ring,
    reflect,reflect]
  generalize kernel s = G
  ring_nf

structure ArcBounds (G D : ℝ → ℝ) (K : ℝ) : Prop where
  hasDeriv : ∀ x, HasDerivAt G (D x) x
  nonnegative : 0 ≤ K
  center : D 0 = 0
  half : D (1/2) = 0
  decreasing : ∀ t ∈ Icc (0:ℝ) (1/2), D t ≤ 0
  lipschitz : ∀ x y, |D x-D y| ≤ K*|x-y|

private theorem interaction_le {G D : ℝ → ℝ} {K h arc u δ : ℝ}
    (H : ArcBounds G D K) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (h₁ : arc ≤ 1) (h₂ : arc ≤ 1/2+δ) (hu : 0 ≤ u) (hv : u+h ≤ arc) :
    interaction G h arc u ≤ K*δ*h :=
  residual_pair_first_difference H.hasDeriv H.nonnegative hδ h₁ h₂ hu hh hv
    H.half H.decreasing H.lipschitz

theorem sameArc_energy_lower {s h r u v K : ℝ} {D : ℝ → ℝ}
    (H : ArcBounds (kernel s) D K) (hh : 0 ≤ h) (hr : r ≤ 1)
    (hu : 0 ≤ u) (hu' : u+h ≤ r) (hv : 0 ≤ v) (hv' : v+h ≤ r) :
    1+(kernel s r-kernel s 0)/3 -
      (2*K*h^2+2*K*|r-1/2| * h)/3 ≤ imageEnergy s (sameArcCell h r u v) := by
  have ha : r ≤ 1/2+|r-1/2| := by linarith [le_abs_self (r-1/2)]
  have h₁ := interaction_le H hh (abs_nonneg _) hr ha hu hu'
  have h₂ := interaction_le H hh (abs_nonneg _) hr ha hv hv'
  have h₃ := centeredDifference_bound H.hasDeriv hh H.lipschitz (v-u)
  have h₄ := opposite_pair_self_score H.hasDeriv H.center hh H.lipschitz
  rw [imageEnergy_eq_pairScore (by decide), sameArc_score]
  norm_num
  linarith [(abs_le.mp h₃).1]

theorem splitArc_energy_lower {s h r u v K : ℝ} {D : ℝ → ℝ}
    (H : ArcBounds (kernel s) D K) (hh : 0 ≤ h) (hr : 0 ≤ r) (hr' : r ≤ 1)
    (hu : 0 ≤ u) (hu' : u+h ≤ r) (hv : 0 ≤ v) (hv' : v+h ≤ 1-r) :
    1+(kernel s r-kernel s 0)/3 -
      (2*K*h^2+2*K*|r-1/2| * h)/3 ≤ imageEnergy s (splitArcCell h r u v) := by
  have ha : r ≤ 1/2+|r-1/2| := by linarith [le_abs_self (r-1/2)]
  have hb : 1-r ≤ 1/2+|r-1/2| := by linarith [neg_abs_le (r-1/2)]
  have h₁ := interaction_le H hh (abs_nonneg _) hr' ha hu hu'
  have h₂ := interaction_le H hh (abs_nonneg _) (show 1-r ≤ 1 by linarith) hb hv hv'
  have h₃ := centeredDifference_bound H.hasDeriv hh H.lipschitz (r+v-u)
  have h₄ := opposite_pair_self_score H.hasDeriv H.center hh H.lipschitz
  rw [imageEnergy_eq_pairScore (by decide), splitArc_score]
  norm_num
  linarith [(abs_le.mp h₃).2]

/-- Every two disjoint edges of a hexagon can be recut into one of the two
coordinate forms. Labels 1 and 3 are the two contacts in the first form;
labels 1 and 4 are the contacts in the second. -/
theorem recut_disjoint_edges (i j : Fin 6) (hne : i ≠ j) (h₁ : i+1 ≠ j) (h₂ : j+1 ≠ i) :
    ∃ k : Fin 6, ((1+k=i ∧ 3+k=j) ∨ (1+k=j ∧ 3+k=i)) ∨ (1+k=i ∧ 4+k=j) := by
  exact (by decide : ∀ i j : Fin 6, i ≠ j → i+1 ≠ j → j+1 ≠ i →
    ∃ k : Fin 6, ((1+k=i ∧ 3+k=j) ∨ (1+k=j ∧ 3+k=i)) ∨ (1+k=i ∧ 4+k=j))
    i j hne h₁ h₂

private theorem gap_values (x : Fin 6 → ℝ) :
    gap (by decide) x =
      ![x 1-x 0, x 2-x 1, x 3-x 2, x 4-x 3, x 5-x 4, x 0+1-x 5] := by
  funext i
  rw [six_gap_eq]
  fin_cases i
  · change x 1-x 0+0=x 1-x 0; ring
  · change x 2-x 1+0=x 2-x 1; ring
  · change x 3-x 2+0=x 3-x 2; ring
  · change x 4-x 3+0=x 4-x 3; ring
  · change x 5-x 4+0=x 5-x 4; ring
  · change x 0-x 5+1=x 0+1-x 5; ring

private theorem nonneg_differences {h : ℝ} {x : Fin 6 → ℝ}
    (hx : Feasible (by decide) h x) (hh : 0 ≤ h) :
    x 0 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ x 5 ∧ x 5 ≤ x 0+1 := by
  have he (i : Fin 6) := hh.trans (hx i)
  simp_rw [gap_values] at he
  exact ⟨sub_nonneg.mp (he 0),sub_nonneg.mp (he 1),sub_nonneg.mp (he 2),
    sub_nonneg.mp (he 3),sub_nonneg.mp (he 4),sub_nonneg.mp (he 5)⟩

/-- Energy lower bound for *every* feasible cell containing two disjoint
contacts. The remaining arc parameter is explicitly bounded by one period. -/
theorem two_dipoles_energy_lower {s h K : ℝ} {D : ℝ → ℝ}
    (H : ArcBounds (kernel s) D K) (hh : 0 ≤ h) (x : Fin 6 → ℝ)
    (hx : Feasible (by decide) h x) (i j : Fin 6) (hi : gap (by decide) x i = h)
    (hj : gap (by decide) x j = h) (hne : i ≠ j) (h₁ : i+1 ≠ j) (h₂ : j+1 ≠ i) :
    ∃ r ∈ Icc (0:ℝ) 1, 1+(kernel s r-kernel s 0)/3 -
      (2*K*h^2+2*K*|r-1/2| * h)/3 ≤ imageEnergy s x := by
  obtain ⟨k,hk⟩ := recut_disjoint_edges i j hne h₁ h₂
  let y := shiftLifts (by decide) x k
  have hy : Feasible (by decide) h y := (feasible_shiftLifts_iff (by decide) h x k).2 hx
  obtain ⟨h01,h12,h23,h34,h45,h50⟩ := nonneg_differences hy hh
  have hv (a : Fin 6) : gap (by decide) y a = gap (by decide) x (a+k) :=
    gap_shiftLifts _ _ _ _
  have h1y : gap (by decide) y 1 = h := by
    rw [hv]
    rcases hk with (⟨he,_⟩ | ⟨he,_⟩) | ⟨he,_⟩ <;> rw [he] <;> assumption
  have h1 : y 2 - y 1 = h := by simpa [gap_values] using h1y
  have hyE : imageEnergy s x = imageEnergy s (fun a => y a + -y 0) := by
    rw [imageEnergy_translate]
    exact (imageEnergy_shiftLifts (by decide) (by decide) s x k).symm
  rw [hyE]
  rcases hk with same | split
  · have h3y : gap (by decide) y 3 = h := by
      rw [hv]
      rcases same with ⟨_,he⟩ | ⟨_,he⟩ <;> rw [he] <;> assumption
    have h3 : y 4 - y 3 = h := by simpa [gap_values] using h3y
    have well : (fun a => y a + -y 0) =
        sameArcCell h (y 5-y 0) (y 1-y 0) (y 3-y 0) := by
      funext a; fin_cases a <;> simp [sameArcCell] <;> linarith
    rw [well]
    exact ⟨_,⟨by linarith,by linarith⟩,
      sameArc_energy_lower H hh (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)⟩
  · have h4y : gap (by decide) y 4 = h := by rw [hv, split.2, hj]
    have h4 : y 5 - y 4 = h := by simpa [gap_values] using h4y
    have well : (fun a => y a + -y 0) =
        splitArcCell h (y 3-y 0) (y 1-y 0) (y 4-y 3) := by
      funext a; fin_cases a <;> simp [splitArcCell] <;> linarith
    rw [well]
    exact ⟨_,⟨by linarith,by linarith⟩,
      splitArc_energy_lower H hh (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)⟩

/-- Uniform loss versus the antipodal collision dipole for the nine classes.
Here the two global scalar bounds on the actual Gaussian kernel are explicit. -/
theorem nine_words_energy_lower {s h K : ℝ} {D : ℝ → ℝ}
    (H : ArcBounds (kernel s) D K) (hh : 0 ≤ h)
    (gain : ∀ r ∈ Icc (0:ℝ) 1, |r-1/2|^2/2 ≤ kernel s r - kernel s (1/2))
    (x : Fin 6 → ℝ) (hx : Feasible (by decide) h x)
    (i j : Fin 6) (hi : gap (by decide) x i = h) (hj : gap (by decide) x j = h)
    (hne : i ≠ j) (h₁ : i+1 ≠ j) (h₂ : j+1 ≠ i) :
    1+(kernel s (1/2)-kernel s 0)/3 - (2*K^2+2*K)*h^2/3 ≤ imageEnergy s x := by
  obtain ⟨r,hr,he⟩ := two_dipoles_energy_lower H hh x hx i j hi hj hne h₁ h₂
  nlinarith [gain r hr, sq_nonneg (|r-1/2|-2*K*h)]


end
end GaussianChains.Point22
