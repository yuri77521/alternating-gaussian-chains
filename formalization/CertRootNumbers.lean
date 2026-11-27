import CertRootInputs
import CertRootExp

/-! The two rational endpoints from the frozen theorem. Both comparisons below
are kernel reductions of rational enclosures, including the two infinite tails. -/
namespace GaussianChains.Root22
open GaussianChains.CertExp

/-- The nine resolved images plus both infinite tails. -/
def derivativeBox (d : ℚ) : Box :=
  addBox (retained negExpBox d) (-tailRadius, tailRadius)

def slopeBox (r : ℚ) : Box :=
  subBox (addBox (subBox (subBox (derivativeBox r) (derivativeBox (r-1/1000)))
    (derivativeBox (r+1/1000))) (derivativeBox (1/2-r))) (derivativeBox (1-2*r))

/-- Check the requested strict sign against both endpoints of the enclosure. -/
def signCheck (b : Box) (positive : Bool) : Bool :=
  if positive then decide (0 < b.1) else decide (b.2 < 0)

theorem signCheck_pos_sound {b : Box} {y : ℝ} (hy : Encloses b y)
    (h : signCheck b true = true) : 0 < y := by
  have hq : 0 < b.1 := by simpa [signCheck] using h
  exact (by exact_mod_cast hq : (0:ℝ) < (b.1:ℝ)).trans_le hy.1

theorem signCheck_neg_sound {b : Box} {y : ℝ} (hy : Encloses b y)
    (h : signCheck b false = true) : y < 0 := by
  have hq : b.2 < 0 := by simpa [signCheck] using h
  exact hy.2.trans_lt (by exact_mod_cast hq : (b.2:ℝ) < 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_lower : signCheck (slopeBox lowerRoot) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_upper : signCheck (slopeBox upperRoot) false = true := by decide +kernel

end GaussianChains.Root22
