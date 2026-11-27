import StripTheoremAssembly
import BandRowsVerified

namespace GaussianChains.Strip

/-- Theorem 5 of the frozen study. All six-particle minimizers on the closed
width strip, with the physical derivative and collision-closure clauses. -/
theorem theorem_five : TheoremFive :=
  theorem_five_of_excluded_rows Band.rowExcluded

#print axioms theorem_five

end GaussianChains.Strip

