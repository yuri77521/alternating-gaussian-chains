/-! Four endpoint lookups and the integer monotonicity checks used in the strip replay. -/
namespace GaussianChains.Band.Fast
/-- Clamp a turning index to a closed subquery of the table. -/
def clamp (k l r : Nat) := max l (min k r)

def range (raw : Nat → Int) (k₁ k₂ l r : Nat) : Int × Int :=
  let a := raw l
  let b := raw r
  let c := raw (clamp k₁ l r)
  let d := raw (clamp k₂ l r)
  (min (min a b) (min c d), max (max a b) (max c d))

def direction (k₁ k₂ : Nat) (up₁ up₂ up₃ : Bool) (i : Nat) : Bool :=
  if i < k₁ then up₁ else if i < k₂ then up₂ else up₃

/-- The direction is selected by the *left* index of an adjacent comparison. -/
def edgeOK (raw : Nat → Int) (k₁ k₂ : Nat) (up₁ up₂ up₃ : Bool) (i : Nat) : Bool :=
  if direction k₁ k₂ up₁ up₂ up₃ i then decide (raw i ≤ raw (i+1))
  else decide (raw (i+1) ≤ raw i)

def checkChunk (raw : Nat → Int) (k₁ k₂ : Nat) (up₁ up₂ up₃ : Bool)
    (first count : Nat) : Bool :=
  (List.range count).all fun j => edgeOK raw k₁ k₂ up₁ up₂ up₃ (first+j)


end GaussianChains.Band.Fast
