import Point22AtlasRangeGroup212Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf212
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .second

theorem s8192_256 : Run get 8192 256 ⟨-581744767,1517693121⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨-2495391421,-589605030⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨-4206102751,-2502472925⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨-5709303410,-4212380071⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨-7004095869,-5714766093⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨-8092914152,-7008747183⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨-8981137834,-8096769643⟩ :=
  of_check (by decide +kernel)

theorem s9984_16 : Run get 9984 16 ⟨-9030159905,-8984223755⟩ :=
  of_check (by decide +kernel)

theorem s10000_4 : Run get 10000 4 ⟨-9042297972,-9033198815⟩ :=
  of_check (by decide +kernel)

theorem s10004_1 : Run get 10004 1 ⟨-9045325159,-9045325153⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨-9676679315,-8984223755⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨-10189556834,-9679030984⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨-10531464837,-10191216950⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨-10715352216,-10532481811⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨-10757948986,-10715778553⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨-10754908449,-10664730117⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨-10664141503,-10458880343⟩ :=
  of_check (by decide +kernel)

theorem s11776_128 : Run get 11776 128 ⟨-10457868377,-10317072537⟩ :=
  of_check (by decide +kernel)

theorem s11904_64 : Run get 11904 64 ⟨-10315869539,-10237213071⟩ :=
  of_check (by decide +kernel)

theorem s11968_16 : Run get 11968 16 ⟨-10235919617,-10216351717⟩ :=
  of_check (by decide +kernel)

theorem s11984_8 : Run get 11984 8 ⟨-10215036168,-10205788854⟩ :=
  of_check (by decide +kernel)

theorem s11992_1 : Run get 11992 1 ⟨-10204462335,-10204462329⟩ :=
  of_check (by decide +kernel)

theorem s9984_32 : Run get 9984 32 ⟨-9078430859,-8984223755⟩ :=
  of_check (by decide +kernel)

theorem s10016_16 : Run get 10016 16 ⟨-9125952959,-9081422900⟩ :=
  of_check (by decide +kernel)

theorem s10032_4 : Run get 10032 4 ⟨-9137716744,-9128898272⟩ :=
  of_check (by decide +kernel)

theorem s10036_1 : Run get 10036 1 ⟨-9140650403,-9140650397⟩ :=
  of_check (by decide +kernel)

theorem s11968_32 : Run get 11968 32 ⟨-10235919617,-10195138418⟩ :=
  of_check (by decide +kernel)

theorem s12000_16 : Run get 12000 16 ⟨-10193800983,-10173576485⟩ :=
  of_check (by decide +kernel)

theorem s12016_8 : Run get 12016 8 ⟨-10172217370,-10162665811⟩ :=
  of_check (by decide +kernel)

theorem s12024_1 : Run get 12024 1 ⟨-10161295934,-10161295928⟩ :=
  of_check (by decide +kernel)

theorem s9984_64 : Run get 9984 64 ⟨-9172728499,-8984223755⟩ :=
  of_check (by decide +kernel)

theorem s10048_16 : Run get 10048 16 ⟨-9218759804,-9175627229⟩ :=
  of_check (by decide +kernel)

theorem s10064_4 : Run get 10064 4 ⟨-9230151620,-9221612098⟩ :=
  of_check (by decide +kernel)

theorem s10068_1 : Run get 10068 1 ⟨-9232992333,-9232992327⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨-10457868377,-10151669215⟩ :=
  of_check (by decide +kernel)

theorem s12032_16 : Run get 12032 16 ⟨-10150288625,-10129419896⟩ :=
  of_check (by decide +kernel)

theorem s12048_8 : Run get 12048 8 ⟨-10128018037,-10118167992⟩ :=
  of_check (by decide +kernel)

theorem s12056_1 : Run get 12056 1 ⟨-10116755576,-10116755570⟩ :=
  of_check (by decide +kernel)

theorem s10004_4 : Run get 10004 4 ⟨-9054389131,-9045325153⟩ :=
  of_check (by decide +kernel)

theorem s10008_8 : Run get 10008 8 ⟨-9078430859,-9057404589⟩ :=
  of_check (by decide +kernel)

theorem s10016_32 : Run get 10016 32 ⟨-9172728499,-9081422900⟩ :=
  of_check (by decide +kernel)

theorem s10048_64 : Run get 10048 64 ⟨-9352412016,-9175627229⟩ :=
  of_check (by decide +kernel)

theorem s10112_128 : Run get 10112 128 ⟨-9676679315,-9355125897⟩ :=
  of_check (by decide +kernel)

theorem s10036_4 : Run get 10036 4 ⟨-9149433904,-9140650397⟩ :=
  of_check (by decide +kernel)

theorem s10040_8 : Run get 10040 8 ⟨-9172728499,-9152355908⟩ :=
  of_check (by decide +kernel)

theorem s10068_4 : Run get 10068 4 ⟨-9241497104,-9232992327⟩ :=
  of_check (by decide +kernel)

theorem s10072_8 : Run get 10072 8 ⟨-9264049231,-9244326234⟩ :=
  of_check (by decide +kernel)

theorem s10080_32 : Run get 10080 32 ⟨-9352412016,-9266855235⟩ :=
  of_check (by decide +kernel)

theorem s11992_8 : Run get 11992 8 ⟨-10204462335,-10195138418⟩ :=
  of_check (by decide +kernel)

theorem s12000_32 : Run get 12000 32 ⟨-10193800983,-10151669215⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨-10150288625,-9756835627⟩ :=
  of_check (by decide +kernel)

theorem s12024_8 : Run get 12024 8 ⟨-10161295934,-10151669215⟩ :=
  of_check (by decide +kernel)

theorem s12056_8 : Run get 12056 8 ⟨-10116755576,-10106831805⟩ :=
  of_check (by decide +kernel)

theorem s12064_32 : Run get 12064 32 ⟨-10105408882,-10060652361⟩ :=
  of_check (by decide +kernel)

theorem s12096_64 : Run get 12096 64 ⟨-10059187919,-9964371173⟩ :=
  of_check (by decide +kernel)

theorem s12160_128 : Run get 12160 128 ⟨-9962826116,-9756835627⟩ :=
  of_check (by decide +kernel)

theorem s12088_8 : Run get 12088 8 ⟨-10070867474,-10060652361⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf212
