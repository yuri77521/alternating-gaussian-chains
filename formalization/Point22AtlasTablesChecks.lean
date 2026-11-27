import Point22AtlasTablesCheck
import Point22AtlasTablesNodes
import Point22AtlasTablesSamples
import Point22AtlasNodeData

/-! Reduction of the literal-table claim to bounded integer checks. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.Cert GaussianChains.Cert.Nodes GaussianChains.ImageBounds

def traceOK := bandOK savedSample restart

def rowOK (p : ℕ) : Bool :=
  decide (verifiedRow .value p = row savedSample .value p ∧
    verifiedRow .first p = row savedSample .first p ∧
    verifiedRow .second p = row savedSample .second p)

theorem restart_zero : restart 0 = init := by decide +kernel
theorem sample_last : savedSample 128000 = (restart 2000).sample := by decide +kernel

theorem verifiedRow_eq_gridNode_of_checks (hs : Checked traceOK 0 2000)
    (hr : Checked rowOK 0 32000) (j : Order) {p : ℕ} (hp : p < 32000) :
    (verifiedRow j p).decode unit = GaussianChains.Cert.Tables.gridNode work unit grid 22 j p := by
  have h := of_decide_eq_true (hr p (Nat.zero_le _) hp)
  have hj : verifiedRow j p = row savedSample j p := by
    cases j with
    | value => exact h.1
    | first => exact h.2.1
    | second => exact h.2.2
  rw [hj]
  exact row_eq_gridNode (fun _ hn => checkedSamples_eq hs restart_zero sample_last hn) j hp

theorem verifiedRow_sound_of_checks (hs : Checked traceOK 0 2000)
    (hr : Checked rowOK 0 32000) (j : Order) {p : ℕ} (hp : p < 32000) :
    ((verifiedRow j p).decode unit).Mem ((deriv^[orderIndex j] (kernel 22)) ((p:ℝ)/32000)) := by
  rw [verifiedRow_eq_gridNode_of_checks hs hr j hp]
  exact GaussianChains.Cert.Tables.gridNode_point_sound work unit grid (by decide) j (by exact hp.le)

end GaussianChains.Point22.Atlas.Tables

