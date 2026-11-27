import Point22AtlasRangeGroup410Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s8192_256 : Run get 8192 256 ⟨-538638048,-507362947⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨-507240221,-476005292⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨-475883224,-444935470⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨-444814979,-414375687⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨-414257589,-384521668⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨-384406677,-355542500⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨-355431223,-327580875⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨-327473817,-300753733⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨-300651304,-275153238⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨-275055750,-250848015⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨-250755693,-227884626⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨-227797610,-206289205⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨-206207557,-186069201⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨-185992918,-167215204⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨-167144219,-149702781⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨-149636971,-133494294⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
