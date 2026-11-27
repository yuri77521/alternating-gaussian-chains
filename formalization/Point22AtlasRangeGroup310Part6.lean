import Point22AtlasRangeGroup310Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s24576_256 : Run get 24576 256 ⟨30291925742,32824342765⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨32834498919,35479848868⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨35490436378,38242372795⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨38253363978,41104103884⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨41115465365,44055768157⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨44067460834,47086626850⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨47098605920,50184496168⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨50196711253,53335789463⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨53348184818,56525582614⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨56538097429,59737703006⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨59750271797,62954842033⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨62967395131,66158690577⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨66171154699,69330096412⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨69342395318,72449242005⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨72461297231,75495840665⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨75507572318,78449348529⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
