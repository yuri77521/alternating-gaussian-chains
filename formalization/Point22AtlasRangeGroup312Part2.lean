import Point22AtlasRangeGroup312Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf312
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .second

theorem s8192_256 : Run get 8192 256 ⟨1958821422992,1963903245186⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨1952043518422,1963486986054⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨1925983453557,1951969074874⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨1886962592682,1925855163274⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨1836646026301,1886786933353⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨1776694168570,1836429510489⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨1708737438381,1776443238926⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨1634354128770,1708458374853⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨1555051634466,1634052968655⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨1472251110481,1554734105797⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨1387275545464,1471922578829⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨1301341153712,1386940973945⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨1215551920570,1301005075674⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨1130897078059,1215218424190⟩ :=
  of_check (by decide +kernel)

theorem s11776_128 : Run get 11776 128 ⟨1089272794294,1130569801889⟩ :=
  of_check (by decide +kernel)

theorem s11904_64 : Run get 11904 64 ⟨1068680777349,1088949853403⟩ :=
  of_check (by decide +kernel)

theorem s11968_32 : Run get 11968 32 ⟨1058444985332,1068360286435⟩ :=
  of_check (by decide +kernel)

theorem s12000_16 : Run get 12000 16 ⟨1053342769590,1058125787050⟩ :=
  of_check (by decide +kernel)

theorem s12016_8 : Run get 12016 8 ⟨1050795658691,1053024234168⟩ :=
  of_check (by decide +kernel)

theorem s12024_1 : Run get 12024 1 ⟨1050477458781,1050477458790⟩ :=
  of_check (by decide +kernel)

theorem s9984_64 : Run get 9984 64 ⟨1690683878437,1708458374853⟩ :=
  of_check (by decide +kernel)

theorem s10048_16 : Run get 10048 16 ⟨1686110605693,1690398735811⟩ :=
  of_check (by decide +kernel)

theorem s10064_4 : Run get 10064 4 ⟨1684963647023,1685824001780⟩ :=
  of_check (by decide +kernel)

theorem s10068_1 : Run get 10068 1 ⟨1684676681415,1684676681424⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨1048251241461,1130569801889⟩ :=
  of_check (by decide +kernel)

theorem s12032_16 : Run get 12032 16 ⟨1043170574459,1047933379794⟩ :=
  of_check (by decide +kernel)

theorem s12048_8 : Run get 12048 8 ⟨1040634367653,1042853397336⟩ :=
  of_check (by decide +kernel)

theorem s12056_1 : Run get 12056 1 ⟨1040317536807,1040317536816⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨968376902920,1047933379794⟩ :=
  of_check (by decide +kernel)

theorem s9042_2 : Run get 9042 2 ⟨1914527340710,1914671702510⟩ :=
  of_check (by decide +kernel)

theorem s9044_4 : Run get 9044 4 ⟨1913947999895,1914382789463⟩ :=
  of_check (by decide +kernel)

theorem s9048_8 : Run get 9048 8 ⟨1912780249408,1913802691783⟩ :=
  of_check (by decide +kernel)

theorem s9056_32 : Run get 9056 32 ⟨1907989262312,1912633432339⟩ :=
  of_check (by decide +kernel)

theorem s9088_128 : Run get 9088 128 ⟨1886962592682,1907836473026⟩ :=
  of_check (by decide +kernel)

theorem s9984_32 : Run get 9984 32 ⟨1699759313908,1708458374853⟩ :=
  of_check (by decide +kernel)

theorem s10016_16 : Run get 10016 16 ⟨1695233572440,1699477163898⟩ :=
  of_check (by decide +kernel)

theorem s10032_4 : Run get 10032 4 ⟨1694098379868,1694949914424⟩ :=
  of_check (by decide +kernel)

theorem s10036_1 : Run get 10036 1 ⟨1693814348501,1693814348510⟩ :=
  of_check (by decide +kernel)

theorem s10036_4 : Run get 10036 4 ⟨1692961696117,1693814348510⟩ :=
  of_check (by decide +kernel)

theorem s10040_8 : Run get 10040 8 ⟨1690683878437,1692677292875⟩ :=
  of_check (by decide +kernel)

theorem s10048_64 : Run get 10048 64 ⟨1672253035568,1690398735811⟩ :=
  of_check (by decide +kernel)

theorem s10112_128 : Run get 10112 128 ⟨1634354128770,1671962187008⟩ :=
  of_check (by decide +kernel)

theorem s11008_16 : Run get 11008 16 ⟨1381920709536,1386940973945⟩ :=
  of_check (by decide +kernel)

theorem s11024_4 : Run get 11024 4 ⟨1380581454193,1381585915613⟩ :=
  of_check (by decide +kernel)

theorem s11028_2 : Run get 11028 2 ⟨1379911747598,1380246607424⟩ :=
  of_check (by decide +kernel)

theorem s11030_1 : Run get 11030 1 ⟨1379576874807,1379576874816⟩ :=
  of_check (by decide +kernel)

theorem s10068_4 : Run get 10068 4 ⟨1683815243789,1684676681424⟩ :=
  of_check (by decide +kernel)

theorem s10072_8 : Run get 10072 8 ⟨1681514126849,1683527917957⟩ :=
  of_check (by decide +kernel)

theorem s10080_32 : Run get 10080 32 ⟨1672253035568,1681226084902⟩ :=
  of_check (by decide +kernel)

theorem s11008_32 : Run get 11008 32 ⟨1376562447313,1386940973945⟩ :=
  of_check (by decide +kernel)

theorem s11040_16 : Run get 11040 16 ⟨1371201039683,1376227448592⟩ :=
  of_check (by decide +kernel)

theorem s11056_4 : Run get 11056 4 ⟨1369860229056,1370865853658⟩ :=
  of_check (by decide +kernel)

theorem s11060_2 : Run get 11060 2 ⟨1369189757926,1369524998928⟩ :=
  of_check (by decide +kernel)

theorem s11062_1 : Run get 11062 1 ⟨1368854506145,1368854506154⟩ :=
  of_check (by decide +kernel)

theorem s11030_2 : Run get 11030 2 ⟨1379241989116,1379576874816⟩ :=
  of_check (by decide +kernel)

theorem s11032_8 : Run get 11032 8 ⟨1376562447313,1378907090599⟩ :=
  of_check (by decide +kernel)

theorem s11040_32 : Run get 11040 32 ⟨1365836765798,1376227448592⟩ :=
  of_check (by decide +kernel)

theorem s11072_64 : Run get 11072 64 ⟨1344356530204,1365501409861⟩ :=
  of_check (by decide +kernel)

theorem s11136_128 : Run get 11136 128 ⟨1301341153712,1344020666352⟩ :=
  of_check (by decide +kernel)

theorem s12024_8 : Run get 12024 8 ⟨1048251241461,1050477458790⟩ :=
  of_check (by decide +kernel)

theorem s12056_8 : Run get 12056 8 ⟨1038100940450,1040317536816⟩ :=
  of_check (by decide +kernel)

theorem s12064_32 : Run get 12064 32 ⟨1027995450676,1037784458557⟩ :=
  of_check (by decide +kernel)

theorem s12096_64 : Run get 12096 64 ⟨1007924247692,1027680390898⟩ :=
  of_check (by decide +kernel)

theorem s12160_128 : Run get 12160 128 ⟨968376902920,1007612155906⟩ :=
  of_check (by decide +kernel)

theorem s12088_8 : Run get 12088 8 ⟨1027995450676,1030202128987⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf312
