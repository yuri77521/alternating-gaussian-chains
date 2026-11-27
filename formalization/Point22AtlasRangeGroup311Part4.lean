import Point22AtlasRangeGroup311Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf311
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .first

theorem s16384_256 : Run get 16384 256 ⟨3977363513,6927979051⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨6939737311,10001396999⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨10013682404,13233117030⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨13246112673,16669945601⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨16683834001,20358488594⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨20373451248,24345012772⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨24361229510,28675252786⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨28692900903,33394156110⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨33413409240,38545559594⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨38566586300,44171792780⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨44194754864,50313205005⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨50338255503,57007615178⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨57034896062,64289685369⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨64319324954,72190221705⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨72222331786,72447378161⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨72479567042,72479567051⟩ :=
  of_check (by decide +kernel)

theorem s16384_128 : Run get 16384 128 ⟨3977363513,5435975132⟩ :=
  of_check (by decide +kernel)

theorem s16512_16 : Run get 16512 16 ⟨5447538578,5621153310⟩ :=
  of_check (by decide +kernel)

theorem s16528_2 : Run get 16528 2 ⟨5632738600,5644325299⟩ :=
  of_check (by decide +kernel)

theorem s16896_128 : Run get 16896 128 ⟨10013682404,11594540438⟩ :=
  of_check (by decide +kernel)

theorem s17024_2 : Run get 17024 2 ⟨11607158103,11619778562⟩ :=
  of_check (by decide +kernel)

theorem s17026_1 : Run get 17026 1 ⟨11632401780,11632401789⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨24361229510,25393577965⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨25410136048,25926139200⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨25942872099,25993103883⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨26009858826,26009858835⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨72222331786,73222634606⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨73255060417,73482318144⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨73514823107,73514823116⟩ :=
  of_check (by decide +kernel)

theorem s17920_128 : Run get 17920 128 ⟨24361229510,26464337190⟩ :=
  of_check (by decide +kernel)

theorem s18048_4 : Run get 18048 4 ⟨26481247654,26532012656⟩ :=
  of_check (by decide +kernel)

theorem s18052_1 : Run get 18052 1 ⟨26548945512,26548945521⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨72222331786,74265172711⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨74297915654,74527394512⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨74560216954,74560216963⟩ :=
  of_check (by decide +kernel)

theorem s16384_16 : Run get 16384 16 ⟨3977363513,4148701049⟩ :=
  of_check (by decide +kernel)

theorem s16400_4 : Run get 16400 4 ⟨4160131660,4194429723⟩ :=
  of_check (by decide +kernel)

theorem s16404_1 : Run get 16404 1 ⟨4205864475,4205864484⟩ :=
  of_check (by decide +kernel)

theorem s16404_4 : Run get 16404 4 ⟨4205864475,4240175024⟩ :=
  of_check (by decide +kernel)

theorem s16408_8 : Run get 16408 8 ⟨4251613958,4331716213⟩ :=
  of_check (by decide +kernel)

theorem s16416_32 : Run get 16416 32 ⟨4343163652,4698581802⟩ :=
  of_check (by decide +kernel)

theorem s16448_64 : Run get 16448 64 ⟨4710065041,5435975132⟩ :=
  of_check (by decide +kernel)

theorem s16529_1 : Run get 16529 1 ⟨5644325290,5644325299⟩ :=
  of_check (by decide +kernel)

theorem s16530_2 : Run get 16530 2 ⟨5655913370,5667502854⟩ :=
  of_check (by decide +kernel)

theorem s16532_4 : Run get 16532 4 ⟨5679093719,5713874758⟩ :=
  of_check (by decide +kernel)

theorem s16536_8 : Run get 16536 8 ⟨5725471241,5806686359⟩ :=
  of_check (by decide +kernel)

theorem s16544_32 : Run get 16544 32 ⟨5818294211,6178862941⟩ :=
  of_check (by decide +kernel)

theorem s16576_64 : Run get 16576 64 ⟨6190518062,6927979051⟩ :=
  of_check (by decide +kernel)

theorem s17026_2 : Run get 17026 2 ⟨11632401780,11645027800⟩ :=
  of_check (by decide +kernel)

theorem s17028_4 : Run get 17028 4 ⟨11657656583,11695559706⟩ :=
  of_check (by decide +kernel)

theorem s17032_8 : Run get 17032 8 ⟨11708199655,11796757878⟩ :=
  of_check (by decide +kernel)

theorem s17040_16 : Run get 17040 16 ⟨11809420292,11999696654⟩ :=
  of_check (by decide +kernel)

theorem s17056_32 : Run get 17056 32 ⟨12012404529,12407783906⟩ :=
  of_check (by decide +kernel)

theorem s17088_64 : Run get 17088 64 ⟨12420584850,13233117030⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨26009858826,26060156812⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨26076933844,26194528096⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨26211349435,26464337190⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨26481247654,28675252786⟩ :=
  of_check (by decide +kernel)

theorem s18944_64 : Run get 18944 64 ⟨44194754864,45657322703⟩ :=
  of_check (by decide +kernel)

theorem s19008_4 : Run get 19008 4 ⟨45680792933,45751251760⟩ :=
  of_check (by decide +kernel)

theorem s19012_2 : Run get 19012 2 ⟨45774754064,45798264411⟩ :=
  of_check (by decide +kernel)

theorem s19014_1 : Run get 19014 1 ⟨45821782765,45821782774⟩ :=
  of_check (by decide +kernel)

theorem s18052_4 : Run get 18052 4 ⟨26548945512,26599777744⟩ :=
  of_check (by decide +kernel)

theorem s18056_8 : Run get 18056 8 ⟨26616733031,26735577470⟩ :=
  of_check (by decide +kernel)

theorem s18064_16 : Run get 18064 16 ⟨26752577748,27008259911⟩ :=
  of_check (by decide +kernel)

theorem s18080_32 : Run get 18080 32 ⟨27025350690,27557995116⟩ :=
  of_check (by decide +kernel)

theorem s18112_64 : Run get 18112 64 ⟨27575268946,28675252786⟩ :=
  of_check (by decide +kernel)

theorem s19014_2 : Run get 19014 2 ⟨45821782765,45845309168⟩ :=
  of_check (by decide +kernel)

theorem s19016_8 : Run get 19016 8 ⟨45868843582,46033809617⟩ :=
  of_check (by decide +kernel)

theorem s19024_16 : Run get 19024 16 ⟨46057408364,46412357165⟩ :=
  of_check (by decide +kernel)

theorem s19040_32 : Run get 19040 32 ⟨46436085011,47175671549⟩ :=
  of_check (by decide +kernel)

theorem s19072_128 : Run get 19072 128 ⟨47199659345,50313205005⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨73514823107,73742635213⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨73775219417,74265172711⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨74297915654,76380800017⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨76414181260,80735408598⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨80770081334,89945984990⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨74560216954,74790252587⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨74823154608,75317880237⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨75350941672,76380800017⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf311
