import PackedFaceTable
import PackedFaceModesEnergy

/-! Physical energy version of the complete minimizing-displacement classification. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

def minimizesEnergy (s h t : ℝ) : Prop :=
  Minimizes (fun v => imageEnergy s (sites h v)) {v | feasible h v} t

theorem minimizesEnergy_iff_score {s : ℝ} (hs : 0 < s) (h t : ℝ) :
    minimizesEnergy s h t ↔
      Minimizes (fun v => phi (Real.exp (-(Real.pi^2)/s)) h (coord v)) {v | feasible h v} t := by
  constructor
  · intro H
    exact ⟨H.1, fun v hv => (imageEnergy_le_iff hs h t v).mp (H.2 v hv)⟩
  · intro H
    exact ⟨H.1, fun v hv => (imageEnergy_le_iff hs h t v).mpr (H.2 v hv)⟩

/-- The four disjoint floor cases of Table 1, including all their equality endpoints. -/
def PhaseRows (s h : ℝ) : Prop :=
    let q := Real.exp (-(Real.pi^2)/s)
    (1/8 < criticalFloor false q ∧ criticalFloor false q < criticalFloor true q ∧
      criticalFloor true q < 1/6) ∧
    (h ≤ criticalFloor false q → ∀ t, minimizesEnergy s h t ↔ t = 0) ∧
    (criticalFloor false q < h → h < criticalFloor true q →
      ∃ t₀ ∈ Ioo 0 (bound h), phiD q h (coord t₀) = 0 ∧
        ∀ t, minimizesEnergy s h t ↔ t = t₀ ∨ t = -t₀) ∧
    (criticalFloor true q ≤ h → h < 1/6 →
      ∀ t, minimizesEnergy s h t ↔ t = bound h ∨ t = -(bound h)) ∧
    (h = 1/6 → ∀ t, minimizesEnergy s h t ↔ t = 0)

/-- Physical-energy classification on the entire closed face. -/
theorem closed_face_energy_table {s h : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ 17/50) (h0 : 0 < h) (h6 : h ≤ 1/6) :
    PhaseRows s h := by
  unfold PhaseRows
  dsimp only
  let q := Real.exp (-(Real.pi^2)/s)
  have hq : 0 < q := Real.exp_pos _
  have hqq : q ≤ faceQ := hQ
  refine ⟨⟨(criticalFloor_spec false hq hqq).1.1,
    criticalFloor_order hq hqq, (criticalFloor_spec true hq hqq).1.2⟩,?_⟩
  simpa only [minimizesEnergy_iff_score hs] using closed_face_score_table hq hqq h0 h6

/-- Strict inequality along every noncentral feasible displacement, including the
degenerate-curvature critical floor needed for the constrained bifurcation. -/
theorem centered_strict_on_face {s h : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ 17/50) (h0 : 0 < h) (h6 : h ≤ 1/6)
    (hc : h ≤ criticalFloor false (Real.exp (-(Real.pi^2)/s)))
    {t : ℝ} (ht : feasible h t) (hne : t ≠ 0) :
    imageEnergy s (sites h 0) < imageEnergy s (sites h t) := by
  have H := (closed_face_energy_table hs hQ h0 h6).2.1 hc
  have H₀ := (H 0).mpr rfl
  apply lt_of_le_of_ne (H₀.2 t ht)
  intro he
  exact hne ((H t).mp ⟨ht, fun v hv => he ▸ H₀.2 v hv⟩)

end GaussianChains.PackedFace


