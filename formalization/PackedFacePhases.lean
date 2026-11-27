import PackedFaceCalculus
import PackedFaceClassification

/-! The closed-face phase table in terms of the two endpoint slopes. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

def centralSlope (q h : ℝ) : ℝ := phiD q h 0
def contactSlope (q h : ℝ) : ℝ := phiD q h (coord (bound h))

private theorem coord_mem_unit (v : ℝ) : coord v ∈ Icc 0 2 := by
  unfold coord
  constructor <;> linarith [Real.cos_le_one (2*Real.pi*v),Real.neg_one_le_cos (2*Real.pi*v)]

private theorem feasible_zero {h : ℝ} (h6 : h ≤ 1/6) : feasible h 0 := by
  simp only [feasible,abs_zero,bound]
  linarith

private theorem feasible_bound {h : ℝ} (h6 : h ≤ 1/6) : feasible h (bound h) := by
  have hge : 0 ≤ bound h := by unfold bound; linarith
  exact (abs_of_nonneg hge).le

private theorem coord_zero_iff {h t : ℝ} (h0 : 0 ≤ h) (h6 : h ≤ 1/6) (ht : feasible h t) :
    coord t = 0 ↔ t = 0 := by
  simpa using coord_eq_iff_reflection h0 ht (feasible_zero h6)

private theorem face_deriv {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    ∀ y ∈ Ioo 0 (coord (bound h)), HasDerivAt (phi q h) (phiD q h y) y := by
  intro y hy
  exact hasDerivAt_phi hq hQ ⟨hy.1,hy.2.trans_le (coord_mem_unit _).2⟩

theorem small_floor_min_iff {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (h0 : 0 ≤ h) (h8 : h ≤ 1/8) (t : ℝ) :
    Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔ t = 0 := by
  have h6 : h ≤ 1/6 := by linarith
  have hz := feasible_zero h6
  have hm := strictMonoOn_phi_small hq hQ h0 h8
  have hmin : ∀ v, feasible h v → v ≠ 0 → phi q h 0 < phi q h (coord v) := by
    intro v hv hn
    exact hm (by constructor <;> norm_num) (coord_mem_unit _) (lt_of_le_of_ne
      (coord_mem_unit _).1 (fun h => hn ((coord_zero_iff h0 h6 hv).mp h.symm)))
  constructor
  · intro H
    by_contra hn
    exact (hmin t H.1 hn).not_ge (by simpa using H.2 0 hz)
  · rintro rfl
    refine ⟨hz,fun v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hn
    · rfl
    · simpa using (hmin v hv hn).le

/-- Nonnegative *left* endpoint derivative gives precisely the centered minimum, including
the first critical point. -/
theorem centered_min_iff {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) (hs : 0 ≤ centralSlope q h) (t : ℝ) :
    Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔ t = 0 := by
  have h0 : 0 ≤ h := by linarith
  by_cases ht : feasible h t
  · rw [minimizes_comp_coord_iff _ h0 h6 ht]
    have hy := coord_mem_unit (bound h)
    rw [min_at_zero_of_leftSlope_nonneg hy.1
      ((continuousOn_phi hq.le hQ).mono (Icc_subset_Icc_right hy.2)) (face_deriv hq.le hQ)
      ((strictMonoOn_phiD_large hq hQ h8 h6).mono (Icc_subset_Icc_right hy.2)) hs]
    exact coord_zero_iff h0 h6 ht
  · constructor
    · intro H
      exact (ht H.1).elim
    · rintro rfl
      exact (ht (feasible_zero h6)).elim

/-- Nonpositive *right* endpoint derivative gives precisely the reflected contact
pair. At the uniform floor the two endpoint displacements coincide. -/
theorem contact_min_iff {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6) (hs : contactSlope q h ≤ 0) (t : ℝ) :
    Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔
      t = bound h ∨ t = -(bound h) := by
  have h0 : 0 ≤ h := by linarith
  have hb := feasible_bound h6
  by_cases ht : feasible h t
  · rw [minimizes_comp_coord_iff _ h0 h6 ht]
    have hy := coord_mem_unit (bound h)
    rw [min_at_end_of_rightSlope_nonpos hy.1
      ((continuousOn_phi hq.le hQ).mono (Icc_subset_Icc_right hy.2)) (face_deriv hq.le hQ)
      ((strictMonoOn_phiD_large hq hQ h8 h6).mono (Icc_subset_Icc_right hy.2)) hs]
    exact coord_eq_iff_reflection h0 ht hb
  · constructor
    · intro H
      exact (ht H.1).elim
    · rintro (rfl | rfl)
      · exact (ht hb).elim
      · exact (ht (by simpa [feasible] using hb)).elim

/-- Opposite signs give a unique interior critical squared displacement and a
single positive physical displacement with its negative. -/
theorem interior_min_pair {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (h8 : 1/8 ≤ h) (h6 : h ≤ 1/6)
    (hl : centralSlope q h < 0) (hr : 0 < contactSlope q h) :
    ∃ t₀ ∈ Ioo 0 (bound h), phiD q h (coord t₀) = 0 ∧
      (∀ z ∈ Icc 0 (coord (bound h)), phiD q h z = 0 ↔ z = coord t₀) ∧
      ∀ t, Minimizes (fun v => phi q h (coord v)) {v | feasible h v} t ↔
        t = t₀ ∨ t = -t₀ := by
  have h0 : 0 ≤ h := by linarith
  have hy := coord_mem_unit (bound h)
  have S := Icc_subset_Icc_right (a := (0:ℝ)) hy.2
  obtain ⟨r, hri, hD, hroot, hmin⟩ := min_at_unique_interior_root hy.1
    ((continuousOn_phi hq.le hQ).mono S) (face_deriv hq.le hQ)
    ((strictMonoOn_phiD_large hq hQ h8 h6).mono S) ((continuousOn_phiD hq.le hQ).mono S) hl hr
  have hrmem := Ioo_subset_Icc_self hri
  rw [← coord_image h h0 h6] at hrmem
  obtain ⟨v,hv,rfl⟩ := hrmem
  have hvf : feasible h v := by simpa [feasible,abs_of_nonneg hv.1] using hv.2
  have hvp : 0 < v := lt_of_le_of_ne hv.1 (fun he => by
    have hz := hri.1
    simpa [← he] using hz)
  have hvb : v < bound h := lt_of_le_of_ne hv.2 (fun he => by
    have hz := hri.2
    simpa [he] using hz)
  refine ⟨v,⟨hvp,hvb⟩,hD,hroot,?_⟩
  intro t
  by_cases ht : feasible h t
  · rw [minimizes_comp_coord_iff _ h0 h6 ht, hmin]
    exact coord_eq_iff_reflection h0 ht hvf
  · constructor
    · intro H
      exact (ht H.1).elim
    · rintro (rfl | rfl)
      · exact (ht hvf).elim
      · exact (ht (by simpa [feasible] using hvf)).elim

theorem uniform_min_iff (F : ℝ → ℝ) (t : ℝ) :
    Minimizes F {v | feasible (1/6) v} t ↔ t = 0 := by
  constructor
  · exact fun H => (feasible_one_sixth_iff t).1 H.1
  · rintro rfl
    exact ⟨(feasible_one_sixth_iff 0).mpr rfl, fun v hv => by rw [(feasible_one_sixth_iff v).1 hv]⟩

end GaussianChains.PackedFace


