import Point22AtlasRangeGroup110Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s24576_256 : Run get 24576 256 ⟨30601522137,33148434542⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨33158646299,35817797662⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨35828437710,38593304371⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨38604344322,41466962161⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨41478367926,44429313600⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨44441045360,47469437415⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨47481449659,50574970974⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨50587212637,53732155322⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨53744570001,56925903487⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨56938429759,60139892421⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨60152464243,63356678421⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨63369225630,66557835432⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨66570284328,69724115126⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨69736389138,72835627147⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨72847647573,75872037422⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨75883724238,78812781986⟩ :=
  of_check (by decide +kernel)

theorem s27864_8 : Run get 27864 8 ⟨69244789008,69330912255⟩ :=
  of_check (by decide +kernel)

theorem s27872_32 : Run get 27872 32 ⟨69343212396,69724115126⟩ :=
  of_check (by decide +kernel)

theorem s27896_8 : Run get 27896 8 ⟨69638173702,69724115126⟩ :=
  of_check (by decide +kernel)

theorem s27928_8 : Run get 27928 8 ⟨70030711835,70116462823⟩ :=
  of_check (by decide +kernel)

theorem s27936_32 : Run get 27936 32 ⟨70128709476,70507915912⟩ :=
  of_check (by decide +kernel)

theorem s27968_64 : Run get 27968 64 ⟨70520133972,71287980013⟩ :=
  of_check (by decide +kernel)

theorem s28032_128 : Run get 28032 128 ⟨71300137172,72835627147⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
