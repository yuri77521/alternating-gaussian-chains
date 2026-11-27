import Point22AtlasRangeGroup330Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s4096_256 : Run get 4096 256 ⟨66581639470,69734676236⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨63381281488,66569193526⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨60165121405,63368736847⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨56951587331,60152551758⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨53758126883,56939062841⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨50601068726,53745713588⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨47495506999,50588828062⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨44455209189,47483495377⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨41492547624,44443477688⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨38618454256,41481141774⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨35842397941,38607413897⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨33172383179,35831757185⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨30614968764,33162170438⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨28175304698,30605206870⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨25857185368,28166011063⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨23663116943,25848372247⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
