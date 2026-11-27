import Point22AtlasRangeGroup112Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf112
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .second

theorem s12288_256 : Run get 12288 256 ⟨882579198727,958262351768⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨810635791531,882289981661⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨743184545483,810363307334⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨680589694569,742930374781⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨623140615639,680355107176⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨571061453307,622926607714⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨524520780237,570868785206⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨483641028942,524350013959⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨448507457934,483492564208⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨419176442764,448381566012⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨395682910677,419073297286⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨378046765496,395602614795⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨366278176708,377989374821⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨360381633312,366243717605⟩ :=
  of_check (by decide +kernel)

theorem s15872_64 : Run get 15872 64 ⟨359825225548,360370116212⟩ :=
  of_check (by decide +kernel)

theorem s15936_1 : Run get 15936 1 ⟨359819444554,359819444557⟩ :=
  of_check (by decide +kernel)

theorem s15936_32 : Run get 15936 32 ⟨359684689020,359819444557⟩ :=
  of_check (by decide +kernel)

theorem s15968_1 : Run get 15968 1 ⟨359681776111,359681776114⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨359635931397,360370116212⟩ :=
  of_check (by decide +kernel)

theorem s16000_1 : Run get 16000 1 ⟨359635886583,359635886586⟩ :=
  of_check (by decide +kernel)

theorem s16000_32 : Run get 16000 32 ⟨359635886583,359678952833⟩ :=
  of_check (by decide +kernel)

theorem s16032_1 : Run get 16032 1 ⟨359681776111,359681776114⟩ :=
  of_check (by decide +kernel)

theorem s13824_64 : Run get 13824 64 ⟨558901551583,570868785206⟩ :=
  of_check (by decide +kernel)

theorem s13888_32 : Run get 13888 32 ⟨552952171976,558714313191⟩ :=
  of_check (by decide +kernel)

theorem s13920_16 : Run get 13920 16 ⟨550010237187,552767660683⟩ :=
  of_check (by decide +kernel)

theorem s13936_8 : Run get 13936 8 ⟨548547472030,549827092359⟩ :=
  of_check (by decide +kernel)

theorem s13944_4 : Run get 13944 4 ⟨547818141663,548365011145⟩ :=
  of_check (by decide +kernel)

theorem s13948_1 : Run get 13948 1 ⟨547636022922,547636022925⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨359635886583,360370116212⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨360370116209,366209348103⟩ :=
  of_check (by decide +kernel)

theorem s13824_128 : Run get 13824 128 ⟨547090180060,570868785206⟩ :=
  of_check (by decide +kernel)

theorem s13952_16 : Run get 13952 16 ⟨544192030528,546908403586⟩ :=
  of_check (by decide +kernel)

theorem s13968_8 : Run get 13968 8 ⟨542751180292,544011624258⟩ :=
  of_check (by decide +kernel)

theorem s13976_4 : Run get 13976 4 ⟨542032812890,542571459806⟩ :=
  of_check (by decide +kernel)

theorem s13980_1 : Run get 13980 1 ⟨541853435461,541853435464⟩ :=
  of_check (by decide +kernel)

theorem s13952_32 : Run get 13952 32 ⟨541315817895,546908403586⟩ :=
  of_check (by decide +kernel)

theorem s13984_16 : Run get 13984 16 ⟨538461570837,541136783640⟩ :=
  of_check (by decide +kernel)

theorem s14000_8 : Run get 14000 8 ⟨537042693191,538283910368⟩ :=
  of_check (by decide +kernel)

theorem s14008_4 : Run get 14008 4 ⟨536335317355,536865720268⟩ :=
  of_check (by decide +kernel)

theorem s14012_1 : Run get 14012 1 ⟨536158688363,536158688366⟩ :=
  of_check (by decide +kernel)

theorem s13952_64 : Run get 13952 64 ⟨535629317415,546908403586⟩ :=
  of_check (by decide +kernel)

theorem s14016_16 : Run get 14016 16 ⟨532819085084,535453032466⟩ :=
  of_check (by decide +kernel)

theorem s14032_8 : Run get 14032 8 ⟨531422235242,532644177351⟩ :=
  of_check (by decide +kernel)

theorem s14040_4 : Run get 14040 4 ⟨530725878353,531248016742⟩ :=
  of_check (by decide +kernel)

theorem s14044_1 : Run get 14044 1 ⟨530552004620,530552004623⟩ :=
  of_check (by decide +kernel)

theorem s12800_128 : Run get 12800 128 ⟨776324017962,810363307334⟩ :=
  of_check (by decide +kernel)

theorem s12928_32 : Run get 12928 32 ⟨767927485380,776060513215⟩ :=
  of_check (by decide +kernel)

theorem s12960_16 : Run get 12960 16 ⟨763756923343,767666282414⟩ :=
  of_check (by decide +kernel)

theorem s12976_8 : Run get 12976 8 ⟨761678606048,763496879386⟩ :=
  of_check (by decide +kernel)

theorem s12984_2 : Run get 12984 2 ⟨761159753910,761419143592⟩ :=
  of_check (by decide +kernel)

theorem s12986_1 : Run get 12986 1 ⟨760900437033,760900437036⟩ :=
  of_check (by decide +kernel)

theorem s12928_64 : Run get 12928 64 ⟨759604945382,776060513215⟩ :=
  of_check (by decide +kernel)

theorem s12992_16 : Run get 12992 16 ⟨755471635937,759346065745⟩ :=
  of_check (by decide +kernel)

theorem s13008_8 : Run get 13008 8 ⟨753412007974,755213925860⟩ :=
  of_check (by decide +kernel)

theorem s13016_2 : Run get 13016 2 ⟨752897834686,753154884618⟩ :=
  of_check (by decide +kernel)

theorem s13018_1 : Run get 13018 1 ⟨752640858207,752640858210⟩ :=
  of_check (by decide +kernel)

theorem s12992_32 : Run get 12992 32 ⟨751357078272,759346065745⟩ :=
  of_check (by decide +kernel)

theorem s13024_16 : Run get 13024 16 ⟨747261354476,751100542918⟩ :=
  of_check (by decide +kernel)

theorem s13040_8 : Run get 13040 8 ⟨745220580616,747005998939⟩ :=
  of_check (by decide +kernel)

theorem s13048_2 : Run get 13048 2 ⟨744711127188,744965816874⟩ :=
  of_check (by decide +kernel)

theorem s13050_1 : Run get 13050 1 ⟨744456511587,744456511590⟩ :=
  of_check (by decide +kernel)

theorem s14848_64 : Run get 14848 64 ⟨412754806324,419073297286⟩ :=
  of_check (by decide +kernel)

theorem s14912_16 : Run get 14912 16 ⟨411206460702,412657365789⟩ :=
  of_check (by decide +kernel)

theorem s14928_8 : Run get 14928 8 ⟨410440851232,411110447290⟩ :=
  of_check (by decide +kernel)

theorem s14936_4 : Run get 14936 4 ⟨410060187619,410345551506⟩ :=
  of_check (by decide +kernel)

theorem s14940_2 : Run get 14940 2 ⟨409870391129,409965244767⟩ :=
  of_check (by decide +kernel)

theorem s14942_1 : Run get 14942 1 ⟨409775626718,409775626721⟩ :=
  of_check (by decide +kernel)

theorem s14912_32 : Run get 14912 32 ⟨409680951530,412657365789⟩ :=
  of_check (by decide +kernel)

theorem s14944_16 : Run get 14944 16 ⟨408178283980,409586365570⟩ :=
  of_check (by decide +kernel)

theorem s14960_8 : Run get 14960 8 ⟨407435517377,408085125789⟩ :=
  of_check (by decide +kernel)

theorem s14968_4 : Run get 14968 4 ⟨407066276135,407343073186⟩ :=
  of_check (by decide +kernel)

theorem s14972_2 : Run get 14972 2 ⟨406882191062,406974188972⟩ :=
  of_check (by decide +kernel)

theorem s14974_1 : Run get 14974 1 ⟨406790282416,406790282419⟩ :=
  of_check (by decide +kernel)

theorem s14848_128 : Run get 14848 128 ⟨406698463033,419073297286⟩ :=
  of_check (by decide +kernel)

theorem s14976_16 : Run get 14976 16 ⟨405241493477,406606732915⟩ :=
  of_check (by decide +kernel)

theorem s14992_8 : Run get 14992 8 ⟨404521579418,405151191727⟩ :=
  of_check (by decide +kernel)

theorem s15000_4 : Run get 15000 4 ⟨404163765315,404431991958⟩ :=
  of_check (by decide +kernel)

theorem s15004_2 : Run get 15004 2 ⟨403985394025,404074535025⟩ :=
  of_check (by decide +kernel)

theorem s15006_1 : Run get 15006 1 ⟨403896342324,403896342327⟩ :=
  of_check (by decide +kernel)

theorem s16000_64 : Run get 16000 64 ⟨359635886583,359813753190⟩ :=
  of_check (by decide +kernel)

theorem s16064_1 : Run get 16064 1 ⟨359819444554,359819444557⟩ :=
  of_check (by decide +kernel)

theorem s12954_2 : Run get 12954 2 ⟨768973019642,769234583702⟩ :=
  of_check (by decide +kernel)

theorem s12956_4 : Run get 12956 4 ⟨767927485380,768711527763⟩ :=
  of_check (by decide +kernel)

theorem s12960_32 : Run get 12960 32 ⟨759604945382,767666282414⟩ :=
  of_check (by decide +kernel)

theorem s12992_64 : Run get 12992 64 ⟨743184545483,759346065745⟩ :=
  of_check (by decide +kernel)

theorem s12986_2 : Run get 12986 2 ⟨760641192977,760900437036⟩ :=
  of_check (by decide +kernel)

theorem s12988_4 : Run get 12988 4 ⟨759604945382,760382021766⟩ :=
  of_check (by decide +kernel)

theorem s13018_2 : Run get 13018 2 ⟨752383955199,752640858210⟩ :=
  of_check (by decide +kernel)

theorem s13020_4 : Run get 13020 4 ⟨751357078272,752127125685⟩ :=
  of_check (by decide +kernel)

theorem s13024_32 : Run get 13024 32 ⟨743184545483,751100542918⟩ :=
  of_check (by decide +kernel)

theorem s13948_4 : Run get 13948 4 ⟨547090180060,547636022925⟩ :=
  of_check (by decide +kernel)

theorem s13952_128 : Run get 13952 128 ⟨524520780237,546908403586⟩ :=
  of_check (by decide +kernel)

theorem s13980_4 : Run get 13980 4 ⟨541315817895,541853435464⟩ :=
  of_check (by decide +kernel)

theorem s13984_32 : Run get 13984 32 ⟨535629317415,541136783640⟩ :=
  of_check (by decide +kernel)

theorem s14016_64 : Run get 14016 64 ⟨524520780237,535453032466⟩ :=
  of_check (by decide +kernel)

theorem s14012_4 : Run get 14012 4 ⟨535629317415,536158688366⟩ :=
  of_check (by decide +kernel)

theorem s14044_4 : Run get 14044 4 ⟨530030900698,530552004623⟩ :=
  of_check (by decide +kernel)

theorem s14048_32 : Run get 14048 32 ⟨524520780237,529857371840⟩ :=
  of_check (by decide +kernel)

theorem s15006_2 : Run get 15006 2 ⟨403807379921,403896342327⟩ :=
  of_check (by decide +kernel)

theorem s15008_32 : Run get 15008 32 ⟨401007738347,403718506820⟩ :=
  of_check (by decide +kernel)

theorem s15040_64 : Run get 15040 64 ⟨395682910677,400921723345⟩ :=
  of_check (by decide +kernel)

theorem s15038_2 : Run get 15038 2 ⟨401007738347,401093842686⟩ :=
  of_check (by decide +kernel)

theorem s15936_64 : Run get 15936 64 ⟨359635931397,359819444557⟩ :=
  of_check (by decide +kernel)

theorem s16000_128 : Run get 16000 128 ⟨359635886583,360358688734⟩ :=
  of_check (by decide +kernel)

theorem s15968_32 : Run get 15968 32 ⟨359635931397,359681776114⟩ :=
  of_check (by decide +kernel)

theorem s16032_32 : Run get 16032 32 ⟨359681776111,359813753190⟩ :=
  of_check (by decide +kernel)

theorem s16064_64 : Run get 16064 64 ⟨359819444554,360358688734⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf112
