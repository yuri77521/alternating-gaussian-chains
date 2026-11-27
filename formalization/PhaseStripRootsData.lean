import PhaseStripRootsWitnesses
import PhaseStripRootsInputs
import PhaseStripRootsSlope

/-! Replay of the ten root enclosures in Table 2. Each comparison covers the
error from the nome, the phase cosine and the entire infinite Gaussian tail. -/
namespace GaussianChains.PhaseStrip

def RootRow.Checks (r : RootRow) : Prop :=
  8 ≤ r.width ∧ r.width ≤ 9 ∧ 1/8 ≤ r.lower ∧ r.lower < r.upper ∧ r.upper ≤ 1/6 ∧
  encloses r.qBox (qInput r.width) ∧ encloses r.xLeft (xInput r.lower) ∧
  encloses r.xRight (xInput r.upper) ∧
  0 < (slopeBox r.outer r.qBox r.xLeft).lo ∧ (slopeBox r.outer r.qBox r.xRight).hi < 0

instance (r : RootRow) : Decidable r.Checks := by
  unfold RootRow.Checks encloses
  infer_instance

def signsChecked (r : RootRow) : Bool := decide r.Checks

section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem width8_accept :
    signsChecked row8Center = true ∧ signsChecked row8Contact = true := by decide +kernel
private theorem width825_accept :
    signsChecked row825Center = true ∧ signsChecked row825Contact = true := by decide +kernel
private theorem width85_accept :
    signsChecked row85Center = true ∧ signsChecked row85Contact = true := by decide +kernel
private theorem width875_accept :
    signsChecked row875Center = true ∧ signsChecked row875Contact = true := by decide +kernel
private theorem width9_accept :
    signsChecked row9Center = true ∧ signsChecked row9Contact = true := by decide +kernel
end

private theorem brackets_accept : rootRows.all signsChecked = true := by
  simp only [rootRows, List.all_cons, List.all_nil, Bool.true_and,
    width8_accept.1, width8_accept.2, width825_accept.1, width825_accept.2,
    width85_accept.1, width85_accept.2, width875_accept.1, width875_accept.2,
    width9_accept.1, width9_accept.2]

theorem table_checked : ∀ r ∈ rootRows, signsChecked r = true :=
  List.all_eq_true.mp brackets_accept

theorem table_checks_spec {r : RootRow} (h : r ∈ rootRows) :
    8 ≤ r.width ∧ r.width ≤ 9 ∧ 1/8 ≤ r.lower ∧ r.lower < r.upper ∧ r.upper ≤ 1/6 ∧
    encloses r.qBox (qInput r.width) ∧ encloses r.xLeft (xInput r.lower) ∧
    encloses r.xRight (xInput r.upper) ∧
    0 < (slopeBox r.outer r.qBox r.xLeft).lo ∧ (slopeBox r.outer r.qBox r.xRight).hi < 0 :=
  of_decide_eq_true (table_checked r h)

/-- Each slab's worst endpoint combination, for the monotonicity argument
enclosing the phase width between the five tabulated widths. -/
theorem table_adjacent_clearance :
    (0.00114 : ℚ) < row825Contact.lower - row8Center.upper ∧
    (0.00114 : ℚ) < row85Contact.lower - row825Center.upper ∧
    (0.00114 : ℚ) < row875Contact.lower - row85Center.upper ∧
    (0.00114 : ℚ) < row9Contact.lower - row875Center.upper := by decide +kernel

end GaussianChains.PhaseStrip
