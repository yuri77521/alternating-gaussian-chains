import Point22AtlasRangeGroup210Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s4096_256 : Run get 4096 256 ⟨-398059550,-392320335⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨-401370453,-398077203⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨-402324972,-401378676⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨-402315175,-401007935⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨-400998578,-397577011⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨-397559641,-392169960⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨-392145176,-384946712⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨-384915161,-376077418⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨-376039782,-365739511⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨-365696492,-354114817⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨-354067131,-341386801⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨-341335164,-327737956⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨-327683077,-313347401⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨-313289968,-298388700⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨-298329381,-283027944⟩ :=
  of_check (by decide +kernel)

theorem s7936_64 : Run get 7936 64 ⟨-282967368,-279143548⟩ :=
  of_check (by decide +kernel)

theorem s8000_16 : Run get 8000 16 ⟨-279082752,-278170341⟩ :=
  of_check (by decide +kernel)

theorem s8016_1 : Run get 8016 1 ⟨-278109495,-278109489⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨-282967368,-267422086⟩ :=
  of_check (by decide +kernel)

theorem s8000_32 : Run get 8000 32 ⟨-279082752,-277196363⟩ :=
  of_check (by decide +kernel)

theorem s8032_16 : Run get 8032 16 ⟨-277135470,-276221649⟩ :=
  of_check (by decide +kernel)

theorem s8048_1 : Run get 8048 1 ⟨-276160713,-276160707⟩ :=
  of_check (by decide +kernel)

theorem s7936_128 : Run get 7936 128 ⟨-282967368,-275246239⟩ :=
  of_check (by decide +kernel)

theorem s8064_16 : Run get 8064 16 ⟨-275185259,-274270167⟩ :=
  of_check (by decide +kernel)

theorem s8080_1 : Run get 8080 1 ⟨-274209146,-274209140⟩ :=
  of_check (by decide +kernel)

theorem s8064_32 : Run get 8064 32 ⟨-275185259,-273293466⟩ :=
  of_check (by decide +kernel)

theorem s8096_16 : Run get 8096 16 ⟨-273232409,-272316175⟩ :=
  of_check (by decide +kernel)

theorem s8112_1 : Run get 8112 1 ⟨-272255083,-272255077⟩ :=
  of_check (by decide +kernel)

theorem s8016_16 : Run get 8016 16 ⟨-278109495,-277196363⟩ :=
  of_check (by decide +kernel)

theorem s8032_32 : Run get 8032 32 ⟨-277135470,-275246239⟩ :=
  of_check (by decide +kernel)

theorem s8064_128 : Run get 8064 128 ⟨-275185259,-267422086⟩ :=
  of_check (by decide +kernel)

theorem s8048_16 : Run get 8048 16 ⟨-276160713,-275246239⟩ :=
  of_check (by decide +kernel)

theorem s8080_16 : Run get 8080 16 ⟨-274209146,-273293466⟩ :=
  of_check (by decide +kernel)

theorem s8096_32 : Run get 8096 32 ⟨-273232409,-271338329⟩ :=
  of_check (by decide +kernel)

theorem s8128_64 : Run get 8128 64 ⟨-271277202,-267422086⟩ :=
  of_check (by decide +kernel)

theorem s8112_16 : Run get 8112 16 ⟨-272255083,-271338329⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
