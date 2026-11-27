import Point22AtlasRangeGroup110Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s4096_256 : Run get 4096 256 ⟨66582732694,69736389141⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨63381772603,66570284331⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨60165036111,63369225633⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨56950956343,60152464246⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨53756985243,56938429762⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨50599455092,53744570004⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨47493462905,50587212640⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨44452778310,47481449662⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨41489775049,44441045363⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨38615385774,41478367929⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨35839079382,38604344325⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨33168859780,35828437713⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨30611284603,33158646302⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨28171502184,30601522140⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨25853304801,28162208146⟩ :=
  of_check (by decide +kernel)

theorem s7936_32 : Run get 7936 32 ⟨25572217292,25844491428⟩ :=
  of_check (by decide +kernel)

theorem s7968_16 : Run get 7968 16 ⟨25432402313,25563464616⟩ :=
  of_check (by decide +kernel)

theorem s7984_1 : Run get 7984 1 ⟨25423680023,25423680026⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨23659196130,25844491428⟩ :=
  of_check (by decide +kernel)

theorem s7984_16 : Run get 7984 16 ⟨25293073741,25423680026⟩ :=
  of_check (by decide +kernel)

theorem s8000_64 : Run get 8000 64 ⟨24740631133,25284381867⟩ :=
  of_check (by decide +kernel)

theorem s8064_128 : Run get 8064 128 ⟨23659196130,24732061144⟩ :=
  of_check (by decide +kernel)

theorem s8016_16 : Run get 8016 16 ⟨25015877375,25145570534⟩ :=
  of_check (by decide +kernel)

theorem s8032_32 : Run get 8032 32 ⟨24740631133,25007246400⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
