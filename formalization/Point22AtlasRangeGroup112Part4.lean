import Point22AtlasRangeGroup112Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf112
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .second

theorem s16384_256 : Run get 16384 256 ⟨366243717602,377932073681⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨377989374818,395522408299⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨395602614792,418970240899⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨419073297283,448255762656⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨448381566009,483344187191⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨483492564205,524179334109⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨524350013956,570676201680⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨570868785203,622712681807⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨622926607711,680120598396⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨680355107173,742676278294⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨742930374778,810090891810⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨810363307331,882000826443⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨882289981658,957958382188⟩ :=
  of_check (by decide +kernel)

theorem s19712_128 : Run get 19712 128 ⟨958262351765,997289966459⟩ :=
  of_check (by decide +kernel)

theorem s19840_64 : Run get 19840 64 ⟨997600504176,1017261391583⟩ :=
  of_check (by decide +kernel)

theorem s19904_8 : Run get 19904 8 ⟨1017574982013,1019771412699⟩ :=
  of_check (by decide +kernel)

theorem s19912_1 : Run get 19912 1 ⟨1020085373408,1020085373411⟩ :=
  of_check (by decide +kernel)

theorem s19904_32 : Run get 19904 32 ⟨1017574982013,1027319113766⟩ :=
  of_check (by decide +kernel)

theorem s19936_8 : Run get 19936 8 ⟨1027634169929,1029840824735⟩ :=
  of_check (by decide +kernel)

theorem s19944_1 : Run get 19944 1 ⟨1030156240879,1030156240882⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨958262351765,1037423098406⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨1037739578808,1039956166569⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨1040272996452,1040272996455⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨1037739578808,1047572005097⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨1047889867430,1050116091274⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨1050434292383,1050434292386⟩ :=
  of_check (by decide +kernel)

theorem s17920_4 : Run get 17920 4 ⟨524350013956,524862572074⟩ :=
  of_check (by decide +kernel)

theorem s17924_1 : Run get 17924 1 ⟨525033597612,525033597615⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨1037739578808,1119754039708⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨1120080321381,1204203380279⟩ :=
  of_check (by decide +kernel)

theorem s17920_32 : Run get 17920 32 ⟨524350013956,529683929213⟩ :=
  of_check (by decide +kernel)

theorem s17952_4 : Run get 17952 4 ⟨529857371837,530378217099⟩ :=
  of_check (by decide +kernel)

theorem s17956_1 : Run get 17956 1 ⟨530552004620,530552004623⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨524350013956,535276833542⟩ :=
  of_check (by decide +kernel)

theorem s17984_4 : Run get 17984 4 ⟨535453032463,535982145374⟩ :=
  of_check (by decide +kernel)

theorem s17988_1 : Run get 17988 1 ⟨536158688363,536158688366⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨535453032463,540957835192⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨541136783637,541674143817⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨541853435461,541853435464⟩ :=
  of_check (by decide +kernel)

theorem s16896_64 : Run get 16896 64 ⟨395602614792,400835797672⟩ :=
  of_check (by decide +kernel)

theorem s16960_32 : Run get 16960 32 ⟨400921723342,403629723015⟩ :=
  of_check (by decide +kernel)

theorem s16992_2 : Run get 16992 2 ⟨403718506817,403807379924⟩ :=
  of_check (by decide +kernel)

theorem s16994_1 : Run get 16994 1 ⟨403896342324,403896342327⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨1037739578808,1057764467275⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨1058083668410,1060319225715⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨1060638754715,1060638754718⟩ :=
  of_check (by decide +kernel)

theorem s16930_2 : Run get 16930 2 ⟨398382816949,398466151578⟩ :=
  of_check (by decide +kernel)

theorem s16932_4 : Run get 16932 4 ⟨398549575561,398800383670⟩ :=
  of_check (by decide +kernel)

theorem s16936_8 : Run get 16936 8 ⟨398884165081,399473136870⟩ :=
  of_check (by decide +kernel)

theorem s16944_16 : Run get 16944 16 ⟨399557633094,400835797672⟩ :=
  of_check (by decide +kernel)

theorem s16960_64 : Run get 16960 64 ⟨400921723342,406515092059⟩ :=
  of_check (by decide +kernel)

theorem s17024_128 : Run get 17024 128 ⟨406606732912,418970240899⟩ :=
  of_check (by decide +kernel)

theorem s16962_2 : Run get 16962 2 ⟨401093842683,401180036352⟩ :=
  of_check (by decide +kernel)

theorem s16964_4 : Run get 16964 4 ⟨401266319344,401525704299⟩ :=
  of_check (by decide +kernel)

theorem s16968_8 : Run get 16968 8 ⟨401612344599,402221327742⟩ :=
  of_check (by decide +kernel)

theorem s16976_16 : Run get 16976 16 ⟨402308682608,403629723015⟩ :=
  of_check (by decide +kernel)

theorem s16992_32 : Run get 16992 32 ⟨403718506817,406515092059⟩ :=
  of_check (by decide +kernel)

theorem s16994_2 : Run get 16994 2 ⟨403896342324,403985394028⟩ :=
  of_check (by decide +kernel)

theorem s16996_4 : Run get 16996 4 ⟨404074535022,404342493785⟩ :=
  of_check (by decide +kernel)

theorem s17000_8 : Run get 17000 8 ⟨404431991955,405060979256⟩ :=
  of_check (by decide +kernel)

theorem s17008_16 : Run get 17008 16 ⟨405151191724,406515092059⟩ :=
  of_check (by decide +kernel)

theorem s17026_2 : Run get 17026 2 ⟨406790282416,406882191065⟩ :=
  of_check (by decide +kernel)

theorem s17028_4 : Run get 17028 4 ⟨406974188969,407250718247⟩ :=
  of_check (by decide +kernel)

theorem s17032_8 : Run get 17032 8 ⟨407343073183,407992056841⟩ :=
  of_check (by decide +kernel)

theorem s17040_16 : Run get 17040 16 ⟨408085125786,409491868834⟩ :=
  of_check (by decide +kernel)

theorem s17056_32 : Run get 17056 32 ⟨409586365567,412560014437⟩ :=
  of_check (by decide +kernel)

theorem s17088_64 : Run get 17088 64 ⟨412657365786,418970240899⟩ :=
  of_check (by decide +kernel)

theorem s17924_4 : Run get 17924 4 ⟨525033597612,525547192659⟩ :=
  of_check (by decide +kernel)

theorem s17928_8 : Run get 17928 8 ⟨525718563791,526920580131⟩ :=
  of_check (by decide +kernel)

theorem s17936_16 : Run get 17936 16 ⟨527092642157,529683929213⟩ :=
  of_check (by decide +kernel)

theorem s17952_32 : Run get 17952 32 ⟨529857371837,535276833542⟩ :=
  of_check (by decide +kernel)

theorem s17984_64 : Run get 17984 64 ⟨535453032463,546726712692⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨546908403583,570676201680⟩ :=
  of_check (by decide +kernel)

theorem s17956_4 : Run get 17956 4 ⟨530552004620,531073884422⟩ :=
  of_check (by decide +kernel)

theorem s17960_8 : Run get 17960 8 ⟨531248016739,532469355747⟩ :=
  of_check (by decide +kernel)

theorem s17968_16 : Run get 17968 16 ⟨532644177348,535276833542⟩ :=
  of_check (by decide +kernel)

theorem s17988_4 : Run get 17988 4 ⟨536158688363,536688833316⟩ :=
  of_check (by decide +kernel)

theorem s17992_8 : Run get 17992 8 ⟨536865720265,538106335816⟩ :=
  of_check (by decide +kernel)

theorem s18000_16 : Run get 18000 16 ⟨538283910365,540957835192⟩ :=
  of_check (by decide +kernel)

theorem s18016_32 : Run get 18016 32 ⟨541136783637,546726712692⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨541853435461,542391825071⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨542571459803,543831303684⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨544011624255,546726712692⟩ :=
  of_check (by decide +kernel)

theorem s18052_4 : Run get 18052 4 ⟨547636022922,548182635783⟩ :=
  of_check (by decide +kernel)

theorem s18056_8 : Run get 18056 8 ⟨548365011142,549644032995⟩ :=
  of_check (by decide +kernel)

theorem s18064_16 : Run get 18064 16 ⟨549827092356,552583234735⟩ :=
  of_check (by decide +kernel)

theorem s18080_32 : Run get 18080 32 ⟨552767660680,558527159898⟩ :=
  of_check (by decide +kernel)

theorem s18112_64 : Run get 18112 64 ⟨558714313188,570676201680⟩ :=
  of_check (by decide +kernel)

theorem s19014_2 : Run get 19014 2 ⟨760900437033,761159753913⟩ :=
  of_check (by decide +kernel)

theorem s19016_8 : Run get 19016 8 ⟨761419143589,763236908041⟩ :=
  of_check (by decide +kernel)

theorem s19024_16 : Run get 19024 16 ⟨763496879383,767405151727⟩ :=
  of_check (by decide +kernel)

theorem s19040_32 : Run get 19040 32 ⟨767666282411,775797080064⟩ :=
  of_check (by decide +kernel)

theorem s19072_128 : Run get 19072 128 ⟨776060513212,810090891810⟩ :=
  of_check (by decide +kernel)

theorem s19912_8 : Run get 19912 8 ⟨1020085373408,1022284387110⟩ :=
  of_check (by decide +kernel)

theorem s19920_16 : Run get 19920 16 ⟨1022598715542,1027319113766⟩ :=
  of_check (by decide +kernel)

theorem s19936_32 : Run get 19936 32 ⟨1027634169929,1037423098406⟩ :=
  of_check (by decide +kernel)

theorem s19944_8 : Run get 19944 8 ⟨1030156240879,1032365406443⟩ :=
  of_check (by decide +kernel)

theorem s19952_16 : Run get 19952 16 ⟨1032681179963,1037423098406⟩ :=
  of_check (by decide +kernel)

theorem s19976_8 : Run get 19976 8 ⟨1040272996452,1042492021290⟩ :=
  of_check (by decide +kernel)

theorem s19984_16 : Run get 19984 16 ⟨1042809197997,1047572005097⟩ :=
  of_check (by decide +kernel)

theorem s20000_32 : Run get 20000 32 ⟨1047889867430,1057764467275⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨1058083668410,1078274459996⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨1078596206043,1119754039708⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨1050434292383,1052662878187⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨1052981415364,1057764467275⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨1060638754715,1062876597424⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨1063196451529,1067999092040⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨1068319588024,1078274459996⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf112
