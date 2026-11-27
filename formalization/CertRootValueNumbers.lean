import CertRootInputs
import CertRootExp
import CertTree
import Mathlib.Data.Fin.VecNotation

/-! Directed six-site Gaussian image-energy enclosure and its rational acceptance test. -/
namespace GaussianChains.Root22
open GaussianChains.Cert GaussianChains.CertExp

def clip (q : ℚ) : ℚ := max 0 (min 600 q)

def expRange (b : Interval) : Box :=
  negExpRange (clip b.lo) (clip b.hi)

def singleImage (d : Box) (k : ℤ) : Box :=
  let interval := (⟨d.1, d.2⟩ : Interval).add (Interval.singleton (k : ℚ))
  expRange ((Interval.singleton 22).mul (interval.mul interval))

def kernelBox (d : Box) : Box :=
  addBox (sumBox (Finset.Icc (-4:ℤ) 4) (singleImage d)) (-tailRadius, tailRadius)

def chargeQ (i : Fin 6) : ℚ := (-1:ℚ)^i.val

/-- All 36 ordered label-pair contributions, including the diagonals. -/
def energyBox (coords : Fin 6 → Box) : Box :=
  subBox (1,1) (scaleBox (1/6) (sumBox Finset.univ fun i => sumBox Finset.univ fun j =>
    scaleBox (chargeQ i * chargeQ j) (kernelBox (subBox (coords j) (coords i)))))

def coordinateBoxes : Fin 6 → Box :=
  ![(-1/1000,-1/1000),(0,0),(1/1000,1/1000),(lowerRoot,upperRoot),(1/2,1/2),
    (1-upperRoot,1-lowerRoot)]

def energyLower : ℚ := 66503584451339086827047430 / 10^26
def energyUpper : ℚ := 66503584451339086827047431 / 10^26

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem check_energy :
    energyLower < (energyBox coordinateBoxes).1 ∧ (energyBox coordinateBoxes).2 < energyUpper := by
  decide +kernel


end GaussianChains.Root22
