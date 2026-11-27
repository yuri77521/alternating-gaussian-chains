/-! Integer literals holding equally spaced unsigned words. Only the selected
page and selected word are reduced by a point query. -/
namespace GaussianChains.Band.Fast

def wordAt (width page : Nat) (pages : Nat → Nat) (i : Nat) : Nat :=
  (pages (i / page) >>> (width * (i % page))) % (2 ^ width)

def unpackRaw (packed : Nat) : Int × Int :=
  let lo := (packed / 2 : Nat) - (2^35 : Int)
  (lo, lo + 3 + (packed % 2 : Nat))

end GaussianChains.Band.Fast
