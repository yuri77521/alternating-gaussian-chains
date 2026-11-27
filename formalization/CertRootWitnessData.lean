import CertRootValueNumbers
import CertRootCoordinates

/-! Rational cells, score enclosures, and the intact and damaged exclusion trees. -/
namespace GaussianChains.Root22

def witnessBoxes (v : Fin 6 → ℚ) (i : Fin 6) : Box := (v i, v i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem evalX :
    6671068104073566285/10^19 < (energyBox (witnessBoxes witnessX)).1 ∧
    (energyBox (witnessBoxes witnessX)).2 < 6671068104073566286/10^19 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem evalZ :
    6650358445233044362/10^19 < (energyBox (witnessBoxes witnessZ)).1 ∧
    (energyBox (witnessBoxes witnessZ)).2 < 6650358445233044363/10^19 := by decide +kernel

/-- A positive-width six-dimensional box around the feasible trial X. -/
def nearX : GaussianChains.Cert.Box 6 := fun i =>
  ⟨witnessX i-1/10^6, witnessX i+1/10^6⟩

def trialScoreBox (b : GaussianChains.Cert.Box 6) : GaussianChains.Cert.Interval :=
  let z := subBox (energyBox (witnessBoxes witnessZ)) (energyBox (fun i => ((b i).lo,(b i).hi)))
  ⟨z.1,z.2⟩

def trialOracle (b : GaussianChains.Cert.Box 6) : GaussianChains.Cert.Quantity → GaussianChains.Cert.Interval
  | .score _ => trialScoreBox b
  | _ => ⟨0,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem nearX_accepted :
    GaussianChains.Cert.accept trialOracle none nearX (.leaf (.score 0)) = true := by
  decide +kernel

/-- Bisect the fourth coordinate, preserving the translation gauge of the center. -/
def nearXSplit : GaussianChains.Cert.Tree 6 :=
  .split 3 (witnessX 3) (.leaf (.score 0)) (.leaf (.score 0))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem nearX_split_accepted :
    GaussianChains.Cert.accept trialOracle none nearX nearXSplit = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Removing the second half of that particular certificate fails the checker. -/
theorem nearX_missing_child_rejected :
    GaussianChains.Cert.accept trialOracle none nearX (.split 3 (witnessX 3) (.leaf (.score 0)) .hole) =
      false := by decide +kernel

#print axioms nearX_split_accepted
#print axioms nearX_missing_child_rejected
end GaussianChains.Root22
