import Point22AtlasRangeGroup120Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s20480_256 : Run get 20480 256 ⟨-101756914,-91775910⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨-112463330,-101797391⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨-123854814,-112506494⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨-135919600,-123900638⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨-148635817,-135968017⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨-161970669,-148686722⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨-175879681,-162023910⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨-190306062,-175935062⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨-205180201,-190363336⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨-220419322,-205239071⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨-235927331,-220479438⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨-251594865,-235988291⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨-267299599,-251656217⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨-282906781,-267360840⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨-298270049,-282967362⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨-313232522,-298329375⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
