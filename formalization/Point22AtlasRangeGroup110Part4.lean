import Point22AtlasRangeGroup110Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s16384_256 : Run get 16384 256 ⟨843327366,889664887⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨889893296,960356864⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨960681841,1056393518⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨1056820196,1179275405⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨1179810379,1330876616⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨1331527937,1513442511⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨1514219674,1729586090⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨1730500015,1982282502⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨1983345513,2274861189⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨2276086971,2610995065⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨2612398624,2994686158⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨2996283748,3430247066⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨3432056113,3922277638⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨3924316638,4475636279⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨4477924673,5095405313⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨5097963342,5786849933⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
