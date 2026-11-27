import Point22AtlasRangeGroup420

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s160_32 : Run get 160 32 ⟨99952168348,99967010589⟩ :=
  of_check (by decide +kernel)

theorem s192_64 : Run get 192 64 ⟨99908485349,99951620919⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨99558613085,99907663486⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨98931057334,99556699259⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨98031085810,98928067645⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨96866213831,98027045300⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨95446099822,96861156137⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨93782411974,95440066706⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨91888668664,93775452756⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨89780055651,91880839544⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨87473223512,89771418960⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨84986069118,87463846883⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨82337505110,84976024602⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨79547221566,82326868269⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨76635443989,79536070520⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨73622691780,76623858477⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨70529541155,73610752223⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
