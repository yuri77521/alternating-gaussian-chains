import BandVerifiedCacheInstance

/-! Diagnostic executable for locating a rejected packet before attempting its
kernel proof. No theorem uses this executable's exit status. -/
open GaussianChains.Band

def main (args : List String) : IO UInt32 := do
  let which := args[0]?.getD "0"
  let some s := (match which with
    | "0" => some Slab.narrow
    | "1" => some Slab.lower
    | "2" => some Slab.upper
    | _ => none) | throw (IO.userError "expected slab 0, 1, or 2")
  let lo := ((args[1]?.getD "0").toNat?).getD 0
  let hi := ((args[2]?.getD (toString (18*s.count))).toNat?).getD (18*s.count)
  let cache := Fast.packetCache s
  let mut bad := 0
  let mut tested := 0
  for b in List.finRange s.count do
    for i in List.finRange 18 do
      let index := 18*b.val+i.val
      if lo ≤ index ∧ index < hi then
        tested := tested + 1
        if ! Fast.checkRow s cache b i then
          IO.println s!"rejected floor {b.val} support {i.val}"
          bad := bad + 1
    if lo < 18*(b.val+1) && 18*b.val < hi then
      IO.println s!"finished floor {b.val}, running total {tested}, rejected {bad}"
  IO.println s!"slab {which} tested {tested}, rejected {bad}"
  return if bad = 0 && tested > 0 then 0 else 1
