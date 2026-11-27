import Point22AtlasRangeGroup111Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf111
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .first

theorem s16384_256 : Run get 16384 256 ⟨4342062397,7303269793⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨7315081062,10393178446⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨10405539771,13647249169⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨13660343596,17112270791⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨17126280746,20834817670⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨20849924491,24861104931⟩ :=
  of_check (by decide +kernel)

theorem s17920_4 : Run get 17920 4 ⟨24877488199,24926670036⟩ :=
  of_check (by decide +kernel)

theorem s17924_1 : Run get 17924 1 ⟨24943074661,24943074664⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨24877488199,29236788229⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨29254624866,34006700548⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨34026163659,39214519899⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨39235777328,44902363284⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨44925575884,51110304158⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨51135623752,57875812557⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨57903379597,65233119293⟩ :=
  of_check (by decide +kernel)

theorem s19712_128 : Run get 19712 128 ⟨65263060239,69143335614⟩ :=
  of_check (by decide +kernel)

theorem s19840_64 : Run get 19840 64 ⟨69174505775,71157854396⟩ :=
  of_check (by decide +kernel)

theorem s19904_8 : Run get 19904 8 ⟨71189648711,71412483434⟩ :=
  of_check (by decide +kernel)

theorem s19912_1 : Run get 19912 1 ⟨71444356194,71444356197⟩ :=
  of_check (by decide +kernel)

theorem s17920_32 : Run get 17920 32 ⟨24877488199,25388029195⟩ :=
  of_check (by decide +kernel)

theorem s17952_4 : Run get 17952 4 ⟨25404584525,25454283065⟩ :=
  of_check (by decide +kernel)

theorem s17956_1 : Run get 17956 1 ⟨25470860097,25470860100⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨24877488199,25920502226⟩ :=
  of_check (by decide +kernel)

theorem s17984_4 : Run get 17984 4 ⟨25937232377,25987455898⟩ :=
  of_check (by decide +kernel)

theorem s17988_1 : Run get 17988 1 ⟨26004208096,26004208099⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨25937232377,26458612228⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨26475519954,26526276713⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨26543206828,26543206831⟩ :=
  of_check (by decide +kernel)

theorem s16896_64 : Run get 16896 64 ⟨10405539771,11189475647⟩ :=
  of_check (by decide +kernel)

theorem s16960_2 : Run get 16960 2 ⟨11202003105,11214533256⟩ :=
  of_check (by decide +kernel)

theorem s16962_1 : Run get 16962 1 ⟨11227066090,11227066093⟩ :=
  of_check (by decide +kernel)

theorem s19904_32 : Run get 19904 32 ⟨71189648711,72180140738⟩ :=
  of_check (by decide +kernel)

theorem s19936_8 : Run get 19936 8 ⟨72212249380,72437285670⟩ :=
  of_check (by decide +kernel)

theorem s19944_1 : Run get 19944 1 ⟨72469473121,72469473124⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨65263060239,73212508044⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨73244932458,73472180394⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨73504683972,73504683975⟩ :=
  of_check (by decide +kernel)

theorem s16896_128 : Run get 16896 128 ⟨10405539771,11996765574⟩ :=
  of_check (by decide +kernel)

theorem s17024_2 : Run get 17024 2 ⟨12009470599,12022178496⟩ :=
  of_check (by decide +kernel)

theorem s17026_1 : Run get 17026 1 ⟨12034889254,12034889257⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨73244932458,74255001909⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨74287743498,74517212865⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨74550033961,74550033964⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨73244932458,81839541653⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨81874539062,91134231691⟩ :=
  of_check (by decide +kernel)

theorem s16640_64 : Run get 16640 64 ⟨7315081062,8062920591⟩ :=
  of_check (by decide +kernel)

theorem s16704_8 : Run get 16704 8 ⟨8074852192,8158428775⟩ :=
  of_check (by decide +kernel)

theorem s16712_2 : Run get 16712 2 ⟨8170376224,8182325673⟩ :=
  of_check (by decide +kernel)

theorem s16714_1 : Run get 16714 1 ⟨8194277111,8194277114⟩ :=
  of_check (by decide +kernel)

theorem s17408_32 : Run get 17408 32 ⟨17126280746,17562553811⟩ :=
  of_check (by decide +kernel)

theorem s17440_16 : Run get 17440 16 ⟨17576690986,17789232760⟩ :=
  of_check (by decide +kernel)

theorem s17456_4 : Run get 17456 4 ⟨17803434608,17846064565⟩ :=
  of_check (by decide +kernel)

theorem s18944_4 : Run get 18944 4 ⟨44925575884,44995261358⟩ :=
  of_check (by decide +kernel)

theorem s18948_2 : Run get 18948 2 ⟨45018505739,45041758078⟩ :=
  of_check (by decide +kernel)

theorem s18950_1 : Run get 18950 1 ⟨45065018363,45065018366⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨73244932458,75307666573⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨75340726697,75572426980⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨75605566946,75605566949⟩ :=
  of_check (by decide +kernel)

theorem s16384_64 : Run get 16384 64 ⟨4342062397,5065355634⟩ :=
  of_check (by decide +kernel)

theorem s16448_16 : Run get 16448 16 ⟨5076874683,5249812597⟩ :=
  of_check (by decide +kernel)

theorem s16464_2 : Run get 16464 2 ⟨5261352057,5272892822⟩ :=
  of_check (by decide +kernel)

theorem s16465_1 : Run get 16465 1 ⟨5272892819,5272892822⟩ :=
  of_check (by decide +kernel)

theorem s16466_2 : Run get 16466 2 ⟨5284434883,5295978255⟩ :=
  of_check (by decide +kernel)

theorem s16468_4 : Run get 16468 4 ⟨5307522930,5342164839⟩ :=
  of_check (by decide +kernel)

theorem s16472_8 : Run get 16472 8 ⟨5353714773,5434601500⟩ :=
  of_check (by decide +kernel)

theorem s16480_32 : Run get 16480 32 ⟨5446162087,5805220995⟩ :=
  of_check (by decide +kernel)

theorem s16512_128 : Run get 16512 128 ⟨5816825985,7303269793⟩ :=
  of_check (by decide +kernel)

theorem s16962_2 : Run get 16962 2 ⟨11227066090,11239601622⟩ :=
  of_check (by decide +kernel)

theorem s16964_4 : Run get 16964 4 ⟨11252139843,11289770716⟩ :=
  of_check (by decide +kernel)

theorem s16968_8 : Run get 16968 8 ⟨11302319744,11390238975⟩ :=
  of_check (by decide +kernel)

theorem s16976_16 : Run get 16976 16 ⟨11402809754,11591700786⟩ :=
  of_check (by decide +kernel)

theorem s16992_32 : Run get 16992 32 ⟨11604315598,11996765574⟩ :=
  of_check (by decide +kernel)

theorem s17024_128 : Run get 17024 128 ⟨12009470599,13647249169⟩ :=
  of_check (by decide +kernel)

theorem s17956_4 : Run get 17956 4 ⟨25470860097,25520623807⟩ :=
  of_check (by decide +kernel)

theorem s17960_8 : Run get 17960 8 ⟨25537222584,25653566597⟩ :=
  of_check (by decide +kernel)

theorem s17968_16 : Run get 17968 16 ⟨25670208993,25920502226⟩ :=
  of_check (by decide +kernel)

theorem s17984_64 : Run get 17984 64 ⟨25937232377,27002447189⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨27019535234,29236788229⟩ :=
  of_check (by decide +kernel)

theorem s17988_4 : Run get 17988 4 ⟨26004208096,26054497820⟩ :=
  of_check (by decide +kernel)

theorem s17992_8 : Run get 17992 8 ⟨26071272107,26188847102⟩ :=
  of_check (by decide +kernel)

theorem s18000_16 : Run get 18000 16 ⟨26205665696,26458612228⟩ :=
  of_check (by decide +kernel)

theorem s18016_32 : Run get 18016 32 ⟨26475519954,27002447189⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨26543206828,26594030822⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨26610983370,26729808598⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨26746806141,27002447189⟩ :=
  of_check (by decide +kernel)

theorem s18052_4 : Run get 18052 4 ⟨27087944247,27139310743⟩ :=
  of_check (by decide +kernel)

theorem s18056_8 : Run get 18056 8 ⟨27156444297,27276538963⟩ :=
  of_check (by decide +kernel)

theorem s18064_16 : Run get 18064 16 ⟨27293718196,27552094869⟩ :=
  of_check (by decide +kernel)

theorem s18080_32 : Run get 18080 32 ⟨27569365973,28107642793⟩ :=
  of_check (by decide +kernel)

theorem s18112_64 : Run get 18112 64 ⟨28125099688,29236788229⟩ :=
  of_check (by decide +kernel)

theorem s18950_2 : Run get 18950 2 ⟨45065018363,45088286610⟩ :=
  of_check (by decide +kernel)

theorem s18952_8 : Run get 18952 8 ⟨45111562809,45274719242⟩ :=
  of_check (by decide +kernel)

theorem s18960_16 : Run get 18960 16 ⟨45298059188,45649117155⟩ :=
  of_check (by decide +kernel)

theorem s18976_32 : Run get 18976 32 ⟨45672585037,46404076571⟩ :=
  of_check (by decide +kernel)

theorem s19008_64 : Run get 19008 64 ⟨46427802089,47938911553⟩ :=
  of_check (by decide +kernel)

theorem s19072_128 : Run get 19072 128 ⟨47963159325,51110304158⟩ :=
  of_check (by decide +kernel)

theorem s19944_8 : Run get 19944 8 ⟨72469473121,72695061390⟩ :=
  of_check (by decide +kernel)

theorem s19952_16 : Run get 19952 16 ⟨72727327739,73212508044⟩ :=
  of_check (by decide +kernel)

theorem s19976_8 : Run get 19976 8 ⟨73504683972,73732486360⟩ :=
  of_check (by decide +kernel)

theorem s19984_16 : Run get 19984 16 ⟨73765069188,74255001909⟩ :=
  of_check (by decide +kernel)

theorem s20000_32 : Run get 20000 32 ⟨74287743498,75307666573⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨75340726697,77443678339⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨77477379440,81839541653⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨74550033961,74780060180⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨74812960869,75307666573⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨75605566946,75837826404⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨75871046292,76370544898⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨76403924874,77443678339⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf111
