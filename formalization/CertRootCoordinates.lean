import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs

/-! The two rational six-site trial cells at width 22, in units of the period. -/
namespace GaussianChains.Root22

def witnessX : Fin 6 → ℚ := ![0,125/1000,126/1000,250/1000,500/1000,750/1000]
def witnessZ : Fin 6 → ℚ := ![0,1/1000,2/1000,251/1000,501/1000,751/1000]

end GaussianChains.Root22
