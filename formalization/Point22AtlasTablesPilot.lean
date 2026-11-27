import Point22AtlasTablesChecks

/-! Two actual slices of the archived table, decided by the Lean kernel. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
#time
theorem sample_band_zero : Checked traceOK 0 1 :=
  Checked.of_segment (lo := 0) (count := 1) (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
#time
theorem first_eight_rows : Checked rowOK 0 8 :=
  Checked.of_segment (lo := 0) (count := 8) (by decide +kernel)

/-- Changing the lower value endpoint at the origin is detected by exact
comparison with its seven retained images and the outward tail rounding. -/
theorem flipped_lower_sign_rejected :
    decide ((⟨-(verifiedRow .value 0).lo,(verifiedRow .value 0).hi⟩ : Ticks) =
      row savedSample .value 0) = false := by decide +kernel

/-- Dropping a step while claiming the unchanged outgoing restart state fails. -/
theorem missing_final_sample_rejected :
    checkBand savedSample (restart 1) 63 0 (restart 0) = false := by decide +kernel

#print axioms sample_band_zero
#print axioms first_eight_rows
end GaussianChains.Point22.Atlas.Tables

