import Point22AtlasRangeGroup211Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf211
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .first

theorem s8192_256 : Run get 8192 256 ⟨1959879686,1964150939⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨1951042952,1963466143⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨1924099691,1950964866⟩ :=
  of_check (by decide +kernel)

theorem s8960_32 : Run get 8960 32 ⟨1919793666,1923968158⟩ :=
  of_check (by decide +kernel)

theorem s8992_16 : Run get 8992 16 ⟨1917566324,1919655907⟩ :=
  of_check (by decide +kernel)

theorem s9008_2 : Run get 9008 2 ⟨1917284451,1917425489⟩ :=
  of_check (by decide +kernel)

theorem s9010_1 : Run get 9010 1 ⟨1917143228,1917143234⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨1884298997,1923968158⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨1833306888,1884120502⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨1772782989,1833087943⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨1704355406,1772530032⟩ :=
  of_check (by decide +kernel)

theorem s9984_16 : Run get 9984 16 ⟨1699852550,1704074703⟩ :=
  of_check (by decide +kernel)

theorem s10000_4 : Run get 10000 4 ⟨1698723021,1699570316⟩ :=
  of_check (by decide +kernel)

theorem s10004_1 : Run get 10004 1 ⟨1698440402,1698440408⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨1629598791,1704074703⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨1550015789,1629296364⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨1467021912,1549697346⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨1381933816,1466692794⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨1295960909,1381598961⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨1210200085,1295624823⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨1125633376,1209866827⟩ :=
  of_check (by decide +kernel)

theorem s11776_128 : Run get 11776 128 ⟨1084073318,1125306558⟩ :=
  of_check (by decide +kernel)

theorem s11904_64 : Run get 11904 64 ⟨1063518067,1083750934⟩ :=
  of_check (by decide +kernel)

theorem s11968_16 : Run get 11968 16 ⟨1058404661,1063198180⟩ :=
  of_check (by decide +kernel)

theorem s11984_8 : Run get 11984 8 ⟨1055851892,1058085426⟩ :=
  of_check (by decide +kernel)

theorem s11992_1 : Run get 11992 1 ⟨1055532982,1055532988⟩ :=
  of_check (by decide +kernel)

theorem s9984_32 : Run get 9984 32 ⟨1695325371,1704074703⟩ :=
  of_check (by decide +kernel)

theorem s10016_16 : Run get 10016 16 ⟨1690774244,1695041630⟩ :=
  of_check (by decide +kernel)

theorem s10032_4 : Run get 10032 4 ⟨1689632764,1690489018⟩ :=
  of_check (by decide +kernel)

theorem s10036_1 : Run get 10036 1 ⟨1689347165,1689347171⟩ :=
  of_check (by decide +kernel)

theorem s11968_32 : Run get 11968 32 ⟨1053301774,1063198180⟩ :=
  of_check (by decide +kernel)

theorem s12000_16 : Run get 12000 16 ⟨1048209581,1052983202⟩ :=
  of_check (by decide +kernel)

theorem s12016_8 : Run get 12016 8 ⟨1045667548,1047891684⟩ :=
  of_check (by decide +kernel)

theorem s12024_1 : Run get 12024 1 ⟨1045349986,1045349992⟩ :=
  of_check (by decide +kernel)

theorem s9984_64 : Run get 9984 64 ⟨1686199543,1704074703⟩ :=
  of_check (by decide +kernel)

theorem s10048_16 : Run get 10048 16 ⟨1681601640,1685912855⟩ :=
  of_check (by decide +kernel)

theorem s10064_4 : Run get 10064 4 ⟨1680448583,1681313515⟩ :=
  of_check (by decide +kernel)

theorem s10068_1 : Run get 10068 1 ⟨1680160095,1680160101⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨1043128255,1125306558⟩ :=
  of_check (by decide +kernel)

theorem s12032_16 : Run get 12032 16 ⟨1038057968,1042811043⟩ :=
  of_check (by decide +kernel)

theorem s12048_8 : Run get 12048 8 ⟨1035527018,1037741452⟩ :=
  of_check (by decide +kernel)

theorem s12056_1 : Run get 12056 1 ⟨1035210848,1035210854⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨963440266,1042811043⟩ :=
  of_check (by decide +kernel)

theorem s12032_32 : Run get 12032 32 ⟨1032998891,1042811043⟩ :=
  of_check (by decide +kernel)

theorem s12064_16 : Run get 12064 16 ⟨1027951193,1032683081⟩ :=
  of_check (by decide +kernel)

theorem s12080_8 : Run get 12080 8 ⟨1025431662,1027636099⟩ :=
  of_check (by decide +kernel)

theorem s12088_1 : Run get 12088 1 ⟨1025116924,1025116930⟩ :=
  of_check (by decide +kernel)

theorem s10004_4 : Run get 10004 4 ⟨1697591977,1698440408⟩ :=
  of_check (by decide +kernel)

theorem s10008_8 : Run get 10008 8 ⟨1695325371,1697308987⟩ :=
  of_check (by decide +kernel)

theorem s10016_32 : Run get 10016 32 ⟨1686199543,1695041630⟩ :=
  of_check (by decide +kernel)

theorem s10048_64 : Run get 10048 64 ⟨1667672431,1685912855⟩ :=
  of_check (by decide +kernel)

theorem s10112_128 : Run get 10112 128 ⟨1629598791,1667380131⟩ :=
  of_check (by decide +kernel)

theorem s10036_4 : Run get 10036 4 ⟨1688489817,1689347171⟩ :=
  of_check (by decide +kernel)

theorem s10040_8 : Run get 10040 8 ⟨1686199543,1688203857⟩ :=
  of_check (by decide +kernel)

theorem s10068_4 : Run get 10068 4 ⟨1679294104,1680160101⟩ :=
  of_check (by decide +kernel)

theorem s10072_8 : Run get 10072 8 ⟨1676980906,1679005269⟩ :=
  of_check (by decide +kernel)

theorem s10080_32 : Run get 10080 32 ⟨1667672431,1676691367⟩ :=
  of_check (by decide +kernel)

theorem s11992_8 : Run get 11992 8 ⟨1053301774,1055532988⟩ :=
  of_check (by decide +kernel)

theorem s12000_32 : Run get 12000 32 ⟨1043128255,1052983202⟩ :=
  of_check (by decide +kernel)

theorem s12024_8 : Run get 12024 8 ⟨1043128255,1045349992⟩ :=
  of_check (by decide +kernel)

theorem s12056_8 : Run get 12056 8 ⟨1032998891,1035210854⟩ :=
  of_check (by decide +kernel)

theorem s12064_32 : Run get 12064 32 ⟨1022915038,1032683081⟩ :=
  of_check (by decide +kernel)

theorem s12096_64 : Run get 12096 64 ⟨1002889155,1022600672⟩ :=
  of_check (by decide +kernel)

theorem s12160_128 : Run get 12160 128 ⟨963440266,1002577798⟩ :=
  of_check (by decide +kernel)

theorem s12088_8 : Run get 12088 8 ⟨1022915038,1025116930⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf211
