import Point22AtlasRangeGroup112Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf112
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .second

theorem s8192_256 : Run get 8192 256 ⟨1960615612263,1964161705846⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨1949776370839,1963150380284⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨1921979898651,1949694746720⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨1881429776914,1921845229645⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨1829792435410,1881248552970⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨1768726250296,1829571167463⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨1699856606936,1768471366904⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨1624754179396,1699574363040⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨1544916583848,1624450578018⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨1461753467065,1544597311153⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨1376575003044,1461423840837⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨1290583692260,1376239934320⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨1204869290202,1290247659567⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨1120406635476,1204536325592⟩ :=
  of_check (by decide +kernel)

theorem s11776_128 : Run get 11776 128 ⟨1078917990426,1120080321384⟩ :=
  of_check (by decide +kernel)

theorem s11904_32 : Run get 11904 32 ⟨1068640123756,1078596206046⟩ :=
  of_check (by decide +kernel)

theorem s11936_16 : Run get 11936 16 ⟨1063516346081,1068319588027⟩ :=
  of_check (by decide +kernel)

theorem s11952_8 : Run get 11952 8 ⟨1060958324508,1063196451532⟩ :=
  of_check (by decide +kernel)

theorem s11960_1 : Run get 11960 1 ⟨1060638754715,1060638754718⟩ :=
  of_check (by decide +kernel)

theorem s11904_64 : Run get 11904 64 ⟨1058402910682,1078596206046⟩ :=
  of_check (by decide +kernel)

theorem s11968_32 : Run get 11968 32 ⟨1048207772261,1058083668413⟩ :=
  of_check (by decide +kernel)

theorem s12000_16 : Run get 12000 16 ⟨1043126417873,1047889867433⟩ :=
  of_check (by decide +kernel)

theorem s12016_8 : Run get 12016 8 ⟨1040589869837,1042809198000⟩ :=
  of_check (by decide +kernel)

theorem s12024_1 : Run get 12024 1 ⟨1040272996452,1040272996455⟩ :=
  of_check (by decide +kernel)

theorem s9728_128 : Run get 9728 128 ⟨1735167179750,1768471366904⟩ :=
  of_check (by decide +kernel)

theorem s9856_64 : Run get 9856 64 ⟨1717718576215,1734897848304⟩ :=
  of_check (by decide +kernel)

theorem s9920_32 : Run get 9920 32 ⟨1708837744767,1717442598608⟩ :=
  of_check (by decide +kernel)

theorem s9952_16 : Run get 9952 16 ⟨1704359525399,1708558586798⟩ :=
  of_check (by decide +kernel)

theorem s9968_4 : Run get 9968 4 ⟨1703236096612,1704078812696⟩ :=
  of_check (by decide +kernel)

theorem s9972_1 : Run get 9972 1 ⟨1702954998904,1702954998907⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨1038056103043,1120080321384⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨958566374953,1037739578811⟩ :=
  of_check (by decide +kernel)

theorem s9984_16 : Run get 9984 16 ⟨1695329365497,1699574363040⟩ :=
  of_check (by decide +kernel)

theorem s10000_4 : Run get 10000 4 ⟨1694193798643,1695045613878⟩ :=
  of_check (by decide +kernel)

theorem s10004_1 : Run get 10004 1 ⟨1693909673748,1693909673751⟩ :=
  of_check (by decide +kernel)

theorem s11968_16 : Run get 11968 16 ⟨1053299994361,1058083668413⟩ :=
  of_check (by decide +kernel)

theorem s11984_8 : Run get 11984 8 ⟨1050752535651,1052981415367⟩ :=
  of_check (by decide +kernel)

theorem s11992_1 : Run get 11992 1 ⟨1050434292383,1050434292386⟩ :=
  of_check (by decide +kernel)

theorem s9984_32 : Run get 9984 32 ⟨1690778176080,1699574363040⟩ :=
  of_check (by decide +kernel)

theorem s10016_16 : Run get 10016 16 ⟨1686203412541,1690492940137⟩ :=
  of_check (by decide +kernel)

theorem s10032_4 : Run get 10032 4 ⟨1685056081902,1685916715603⟩ :=
  of_check (by decide +kernel)

theorem s10036_1 : Run get 10036 1 ⟨1684769023348,1684769023351⟩ :=
  of_check (by decide +kernel)

theorem s9984_64 : Run get 9984 64 ⟨1681605447584,1699574363040⟩ :=
  of_check (by decide +kernel)

theorem s10048_16 : Run get 10048 16 ⟨1676984652740,1681317312905⟩ :=
  of_check (by decide +kernel)

theorem s10064_4 : Run get 10064 4 ⟨1675825930285,1676695103502⟩ :=
  of_check (by decide +kernel)

theorem s10068_1 : Run get 10068 1 ⟨1675536031018,1675536031021⟩ :=
  of_check (by decide +kernel)

theorem s8960_32 : Run get 8960 32 ⟨1917574495142,1921845229645⟩ :=
  of_check (by decide +kernel)

theorem s8992_16 : Run get 8992 16 ⟨1915298071635,1917433650363⟩ :=
  of_check (by decide +kernel)

theorem s9008_2 : Run get 9008 2 ⟨1915010092780,1915154177093⟩ :=
  of_check (by decide +kernel)

theorem s9010_1 : Run get 9010 1 ⟨1914865818804,1914865818807⟩ :=
  of_check (by decide +kernel)

theorem s8960_64 : Run get 8960 64 ⟨1912973042689,1921845229645⟩ :=
  of_check (by decide +kernel)

theorem s9024_16 : Run get 9024 16 ⟨1910599815378,1912826123822⟩ :=
  of_check (by decide +kernel)

theorem s9040_2 : Run get 9040 2 ⟨1910299793298,1910449897634⟩ :=
  of_check (by decide +kernel)

theorem s9042_1 : Run get 9042 1 ⟨1910149502481,1910149502484⟩ :=
  of_check (by decide +kernel)

theorem s12032_16 : Run get 12032 16 ⟨1032996997974,1037739578811⟩ :=
  of_check (by decide +kernel)

theorem s12048_8 : Run get 12048 8 ⟨1030471701842,1032681179966⟩ :=
  of_check (by decide +kernel)

theorem s12056_1 : Run get 12056 1 ⟨1030156240879,1030156240882⟩ :=
  of_check (by decide +kernel)

theorem s10752_128 : Run get 10752 128 ⟨1419338399377,1461423840837⟩ :=
  of_check (by decide +kernel)

theorem s10880_64 : Run get 10880 64 ⟨1397990897680,1419005464592⟩ :=
  of_check (by decide +kernel)

theorem s10944_32 : Run get 10944 32 ⟨1387290355257,1397656752498⟩ :=
  of_check (by decide +kernel)

theorem s10976_16 : Run get 10976 16 ⟨1381934388849,1386955712876⟩ :=
  of_check (by decide +kernel)

theorem s10992_4 : Run get 10992 4 ⟨1380594851964,1381599524493⟩ :=
  of_check (by decide +kernel)

theorem s10996_2 : Run get 10996 2 ⟨1379925004757,1380259934870⟩ :=
  of_check (by decide +kernel)

theorem s10998_1 : Run get 10998 1 ⟨1379590061704,1379590061707⟩ :=
  of_check (by decide +kernel)

theorem s12032_32 : Run get 12032 32 ⟨1027949271235,1037739578811⟩ :=
  of_check (by decide +kernel)

theorem s12064_16 : Run get 12064 16 ⟨1022913089763,1027634169932⟩ :=
  of_check (by decide +kernel)

theorem s12080_8 : Run get 12080 8 ⟨1020399380226,1022598715545⟩ :=
  of_check (by decide +kernel)

theorem s12088_1 : Run get 12088 1 ⟨1020085373408,1020085373411⟩ :=
  of_check (by decide +kernel)

theorem s8978_2 : Run get 8978 2 ⟨1919249670695,1919388018830⟩ :=
  of_check (by decide +kernel)

theorem s8980_4 : Run get 8980 4 ⟨1918694352705,1919111129921⟩ :=
  of_check (by decide +kernel)

theorem s8984_8 : Run get 8984 8 ⟨1917574495142,1918555042340⟩ :=
  of_check (by decide +kernel)

theorem s8992_32 : Run get 8992 32 ⟨1912973042689,1917433650363⟩ :=
  of_check (by decide +kernel)

theorem s9024_64 : Run get 9024 64 ⟨1903195016584,1912826123822⟩ :=
  of_check (by decide +kernel)

theorem s9088_128 : Run get 9088 128 ⟨1881429776914,1903036254996⟩ :=
  of_check (by decide +kernel)

theorem s9010_2 : Run get 9010 2 ⟨1914721355260,1914865818807⟩ :=
  of_check (by decide +kernel)

theorem s9012_4 : Run get 9012 4 ⟨1914141607404,1914576702252⟩ :=
  of_check (by decide +kernel)

theorem s9016_8 : Run get 9016 8 ⟨1912973042689,1913996197520⟩ :=
  of_check (by decide +kernel)

theorem s9042_2 : Run get 9042 2 ⟨1909999025278,1910149502484⟩ :=
  of_check (by decide +kernel)

theorem s9044_4 : Run get 9044 4 ⟨1909395254597,1909848361791⟩ :=
  of_check (by decide +kernel)

theorem s9048_8 : Run get 9048 8 ⟨1908178796958,1909243846960⟩ :=
  of_check (by decide +kernel)

theorem s9056_32 : Run get 9056 32 ⟨1903195016584,1908025905795⟩ :=
  of_check (by decide +kernel)

theorem s9972_4 : Run get 9972 4 ⟨1702111130021,1702954998907⟩ :=
  of_check (by decide +kernel)

theorem s9976_8 : Run get 9976 8 ⟨1699856606936,1701829648783⟩ :=
  of_check (by decide +kernel)

theorem s10004_4 : Run get 10004 4 ⟨1693056740893,1693909673751⟩ :=
  of_check (by decide +kernel)

theorem s10008_8 : Run get 10008 8 ⟨1690778176080,1692772244191⟩ :=
  of_check (by decide +kernel)

theorem s10016_32 : Run get 10016 32 ⟨1681605447584,1690492940137⟩ :=
  of_check (by decide +kernel)

theorem s10048_64 : Run get 10048 64 ⟨1662988986343,1681317312905⟩ :=
  of_check (by decide +kernel)

theorem s10112_128 : Run get 10112 128 ⟨1624754179396,1662695331767⟩ :=
  of_check (by decide +kernel)

theorem s10036_4 : Run get 10036 4 ⟨1683907306992,1684769023351⟩ :=
  of_check (by decide +kernel)

theorem s10040_8 : Run get 10040 8 ⟨1681605447584,1683619888280⟩ :=
  of_check (by decide +kernel)

theorem s10068_4 : Run get 10068 4 ⟨1674665809891,1675536031021⟩ :=
  of_check (by decide +kernel)

theorem s10072_8 : Run get 10072 8 ⟨1672341398356,1674375562043⟩ :=
  of_check (by decide +kernel)

theorem s10080_32 : Run get 10080 32 ⟨1662988986343,1672050457667⟩ :=
  of_check (by decide +kernel)

theorem s10966_2 : Run get 10966 2 ⟨1389966967936,1390301477685⟩ :=
  of_check (by decide +kernel)

theorem s10968_8 : Run get 10968 8 ⟨1387290355257,1389632443178⟩ :=
  of_check (by decide +kernel)

theorem s10976_32 : Run get 10976 32 ⟨1376575003044,1386955712876⟩ :=
  of_check (by decide +kernel)

theorem s10998_2 : Run get 10998 2 ⟨1379255105774,1379590061707⟩ :=
  of_check (by decide +kernel)

theorem s11000_8 : Run get 11000 8 ⟨1376575003044,1378920137041⟩ :=
  of_check (by decide +kernel)

theorem s11030_2 : Run get 11030 2 ⟨1368530126957,1368865458835⟩ :=
  of_check (by decide +kernel)

theorem s11032_8 : Run get 11032 8 ⟨1365847095103,1368194784459⟩ :=
  of_check (by decide +kernel)

theorem s11040_32 : Run get 11040 32 ⟨1355108857860,1365511670033⟩ :=
  of_check (by decide +kernel)

theorem s11072_64 : Run get 11072 64 ⟨1333610162337,1354773145571⟩ :=
  of_check (by decide +kernel)

theorem s11136_128 : Run get 11136 128 ⟨1290583692260,1333274079522⟩ :=
  of_check (by decide +kernel)

theorem s11062_2 : Run get 11062 2 ⟨1357794264828,1358129903279⟩ :=
  of_check (by decide +kernel)

theorem s11064_8 : Run get 11064 8 ⟨1355108857860,1357458617910⟩ :=
  of_check (by decide +kernel)

theorem s11960_8 : Run get 11960 8 ⟨1058402910682,1060638754718⟩ :=
  of_check (by decide +kernel)

theorem s11968_64 : Run get 11968 64 ⟨1038056103043,1058083668413⟩ :=
  of_check (by decide +kernel)

theorem s11992_8 : Run get 11992 8 ⟨1048207772261,1050434292386⟩ :=
  of_check (by decide +kernel)

theorem s12000_32 : Run get 12000 32 ⟨1038056103043,1047889867433⟩ :=
  of_check (by decide +kernel)

theorem s12024_8 : Run get 12024 8 ⟨1038056103043,1040272996455⟩ :=
  of_check (by decide +kernel)

theorem s12056_8 : Run get 12056 8 ⟨1027949271235,1030156240882⟩ :=
  of_check (by decide +kernel)

theorem s12064_32 : Run get 12064 32 ⟨1017888618871,1027634169932⟩ :=
  of_check (by decide +kernel)

theorem s12096_64 : Run get 12096 64 ⟨997911090813,1017574982016⟩ :=
  of_check (by decide +kernel)

theorem s12160_128 : Run get 12160 128 ⟨958566374953,997600504179⟩ :=
  of_check (by decide +kernel)

theorem s12088_8 : Run get 12088 8 ⟨1017888618871,1020085373411⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf112
