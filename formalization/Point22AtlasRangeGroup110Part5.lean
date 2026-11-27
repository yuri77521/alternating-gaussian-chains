import Point22AtlasRangeGroup110Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s20480_256 : Run get 20480 256 ⟨5789698463,6555370315⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨6558530635,7406446592⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨7409940185,8345576522⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨8349424810,9378205812⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨9382429868,10509651241⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨10514271472,11745016902⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨11750052714,13089104094⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨13094573524,14546315597⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨14552234932,16120555275⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨16126938650,17815124191⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨17821983181,19632614614⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨19639957816,21574803517⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨21582636135,23642547335⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨23650870774,25835679948⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨25844491425,28152915962⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨28162208143,30591761472⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
