import Point22AtlasRangeGroup210Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s28672_256 : Run get 28672 256 ⟨346008791,361600953⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨327839418,345942691⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨307221364,327763592⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨284257257,307136154⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨259079429,284163124⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨231848839,258976945⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨202753485,231738689⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨172006315,202636452⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨139842673,171883277⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨106517324,139714591⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨72301098,106385225⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨37477233,72166067⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨19928383,37340396⟩ :=
  of_check (by decide +kernel)

theorem s31872_1 : Run get 31872 1 ⟨19791069,19791075⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨15533149,19791075⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨15395762,15395768⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨11135866,19791075⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨6737112,10998430⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨6599634,6599640⟩ :=
  of_check (by decide +kernel)

theorem s31936_1 : Run get 31936 1 ⟨10998424,10998430⟩ :=
  of_check (by decide +kernel)

theorem s29916_4 : Run get 29916 4 ⟨262342486,262646745⟩ :=
  of_check (by decide +kernel)

theorem s29920_32 : Run get 29920 32 ⟨259079429,262241011⟩ :=
  of_check (by decide +kernel)

theorem s29948_4 : Run get 29948 4 ⟨259079429,259386716⟩ :=
  of_check (by decide +kernel)

theorem s29980_4 : Run get 29980 4 ⟨255784262,256094545⟩ :=
  of_check (by decide +kernel)

theorem s29984_32 : Run get 29984 32 ⟨252457332,255680781⟩ :=
  of_check (by decide +kernel)

theorem s30016_64 : Run get 30016 64 ⟨245709591,252352863⟩ :=
  of_check (by decide +kernel)

theorem s30080_128 : Run get 30080 128 ⟨231848839,245603181⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
