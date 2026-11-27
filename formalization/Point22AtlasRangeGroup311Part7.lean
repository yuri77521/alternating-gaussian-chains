import Point22AtlasRangeGroup311Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf311
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .first

theorem s28672_256 : Run get 28672 256 ⟨347023420906,362456326852⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨329010864622,346957934013⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨308544667448,328935636307⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨285725571106,308460032529⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨260684061035,285631981931⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨233579325339,260582084441⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨204597696844,233469637559⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨173950596503,204481076426⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨141872008242,173827915342⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨108615526466,141744220842⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨74451027878,108483657631⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨39661028538,74316159061⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨22122255210,39524283071⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨13333043894,21985001513⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨8935508996,13195644552⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨8798064010,8798064019⟩ :=
  of_check (by decide +kernel)

theorem s29952_16 : Run get 29952 16 ⟨259048660389,260582084441⟩ :=
  of_check (by decide +kernel)

theorem s29968_8 : Run get 29968 8 ⟨258227947718,258946180932⟩ :=
  of_check (by decide +kernel)

theorem s29976_4 : Run get 29976 4 ⟨257816840633,258125217831⟩ :=
  of_check (by decide +kernel)

theorem s29980_1 : Run get 29980 1 ⟨257713985771,257713985780⟩ :=
  of_check (by decide +kernel)

theorem s29948_4 : Run get 29948 4 ⟨260684061035,260989801711⟩ :=
  of_check (by decide +kernel)

theorem s31936_1 : Run get 31936 1 ⟨13195644543,13195644552⟩ :=
  of_check (by decide +kernel)

theorem s29980_4 : Run get 29980 4 ⟨257405233940,257713985780⟩ :=
  of_check (by decide +kernel)

theorem s29984_32 : Run get 29984 32 ⟨254094475688,257302254292⟩ :=
  of_check (by decide +kernel)

theorem s30016_64 : Run get 30016 64 ⟨247378565066,253990503767⟩ :=
  of_check (by decide +kernel)

theorem s30080_128 : Run get 30080 128 ⟨233579325339,247272641766⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf311
