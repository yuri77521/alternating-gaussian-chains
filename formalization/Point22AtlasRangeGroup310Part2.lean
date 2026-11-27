import Point22AtlasRangeGroup310Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s8192_256 : Run get 8192 256 ⟨21844151982,23920190699⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨19885304437,21836256080⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨18051309785,19877898294⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨16340508942,18044388670⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨14750413464,16334064679⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨13277811951,14744434845⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨11918876185,13272285153⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨10669265360,11913785185⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨9524226986,10664592327⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨8478693287,9519952677⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨7527372089,8474797409⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨6664831440,7523833642⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨5885577431,6661629038⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨5184124826,5882689584⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨4555060378,5181530210⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨3993098820,4552738065⟩ :=
  of_check (by decide +kernel)

theorem s12056_8 : Run get 12056 8 ⟨4481252141,4497308645⟩ :=
  of_check (by decide +kernel)

theorem s12064_32 : Run get 12064 32 ⟨4408482009,4478962423⟩ :=
  of_check (by decide +kernel)

theorem s12096_64 : Run get 12096 64 ⟨4266015684,4406224568⟩ :=
  of_check (by decide +kernel)

theorem s12160_128 : Run get 12160 128 ⟨3993098820,4263821856⟩ :=
  of_check (by decide +kernel)

theorem s12088_8 : Run get 12088 8 ⟨4408482009,4424312292⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
