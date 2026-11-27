import Point22AtlasRangeGroup312Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf312
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .second

theorem s16384_256 : Run get 16384 256 ⟨365280096815,376237416489⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨376291851816,393094564424⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨393171909247,415810768462⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨415910971588,444367615961⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨444490581212,478732423128⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨478877986980,518851956241⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨519019861196,529772238441⟩ :=
  of_check (by decide +kernel)

theorem s17984_4 : Run get 17984 4 ⟨529945674579,530466500352⟩ :=
  of_check (by decide +kernel)

theorem s17988_1 : Run get 17988 1 ⟨530640281352,530640281361⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨519019861196,564645125210⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨564834989421,615994799204⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨616206083018,672738921952⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨672970892082,734661132359⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨734912824575,801481124016⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨801751305308,872845003948⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨873132135230,948315935994⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨948618136508,1027365376226⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨1027680390889,1029886754536⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨1030202128978,1030202128987⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨529945674579,535364930866⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨535541123008,536070215545⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨536246751715,536246751724⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨1027680390889,1037468020460⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨1037784458548,1040000749443⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨1040317536807,1040317536816⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨1027680390889,1109365225872⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨1109690396861,1193581239917⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨1027680390889,1047615560587⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨1047933379785,1050159301013⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨1050477458781,1050477458790⟩ :=
  of_check (by decide +kernel)

theorem s17026_2 : Run get 17026 2 ⟨403987782772,404076833392⟩ :=
  of_check (by decide +kernel)

theorem s17028_4 : Run get 17028 4 ⟨404165973288,404433928764⟩ :=
  of_check (by decide +kernel)

theorem s17032_8 : Run get 17032 8 ⟨404523425824,405152405330⟩ :=
  of_check (by decide +kernel)

theorem s17040_16 : Run get 17040 16 ⟨405242616667,406606499793⟩ :=
  of_check (by decide +kernel)

theorem s17056_32 : Run get 17056 32 ⟨406698139469,409583237665⟩ :=
  of_check (by decide +kernel)

theorem s17088_64 : Run get 17088 64 ⟨409677733128,415810768462⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨536246751715,536776876180⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨536953756274,538194323618⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨538371891235,541045711045⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨541224652406,564645125210⟩ :=
  of_check (by decide +kernel)

theorem s18052_4 : Run get 18052 4 ⟨541941275821,542479644031⟩ :=
  of_check (by decide +kernel)

theorem s18056_8 : Run get 18056 8 ⟨542659271601,543919065130⟩ :=
  of_check (by decide +kernel)

theorem s18064_16 : Run get 18064 16 ⟨544099378463,546814357238⟩ :=
  of_check (by decide +kernel)

theorem s18080_32 : Run get 18080 32 ⟨546996040731,552670637858⟩ :=
  of_check (by decide +kernel)

theorem s18112_64 : Run get 18112 64 ⟨552855056088,564645125210⟩ :=
  of_check (by decide +kernel)

theorem s19014_2 : Run get 19014 2 ⟨752716090410,752973046418⟩ :=
  of_check (by decide +kernel)

theorem s19016_8 : Run get 19016 8 ⟨753230075842,755031336300⟩ :=
  of_check (by decide +kernel)

theorem s19024_16 : Run get 19024 16 ⟨755288952459,759161973831⟩ :=
  of_check (by decide +kernel)

theorem s19040_32 : Run get 19040 32 ⟨759420759581,767479187391⟩ :=
  of_check (by decide +kernel)

theorem s19072_128 : Run get 19072 128 ⟨767740296540,801481124016⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨1040317536807,1042536263343⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨1042853397327,1047615560587⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨1047933379785,1068039835234⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨1068360286426,1109365225872⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨1050477458781,1052705740530⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨1053024234159,1057806629865⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨1058125787041,1068039835234⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf312
