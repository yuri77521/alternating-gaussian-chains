import Point22AtlasRangeGroup210Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s20480_256 : Run get 20480 256 ⟨90571372,100467002⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨100507144,111087427⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨111130255,122393723⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨122439215,134375326⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨134423423,147011676⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨147062277,160271385⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨160324345,174111474⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨174166601,188476724⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨188533778,203299149⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨203357837,218497629⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨218557610,233977736⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨234038614,249631758⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨249693088,265338964⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨265400248,280966115⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨281026809,296368247⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨296427764,311389727⟩ :=
  of_check (by decide +kernel)

theorem s23808_128 : Run get 23808 128 ⟨265400248,273171342⟩ :=
  of_check (by decide +kernel)

theorem s23936_16 : Run get 23936 16 ⟨273232403,274148118⟩ :=
  of_check (by decide +kernel)

theorem s23952_1 : Run get 23952 1 ⟨274209140,274209146⟩ :=
  of_check (by decide +kernel)

theorem s23808_64 : Run get 23808 64 ⟨265400248,269258727⟩ :=
  of_check (by decide +kernel)

theorem s23872_32 : Run get 23872 32 ⟨269319916,271216067⟩ :=
  of_check (by decide +kernel)

theorem s23904_16 : Run get 23904 16 ⟨271277196,272193981⟩ :=
  of_check (by decide +kernel)

theorem s23920_1 : Run get 23920 1 ⟨272255077,272255083⟩ :=
  of_check (by decide +kernel)

theorem s23936_32 : Run get 23936 32 ⟨273232403,275124272⟩ :=
  of_check (by decide +kernel)

theorem s23968_16 : Run get 23968 16 ⟨275185253,276099767⟩ :=
  of_check (by decide +kernel)

theorem s23984_1 : Run get 23984 1 ⟨276160707,276160713⟩ :=
  of_check (by decide +kernel)

theorem s23936_64 : Run get 23936 64 ⟨273232403,277074568⟩ :=
  of_check (by decide +kernel)

theorem s24000_16 : Run get 24000 16 ⟨277135464,278048641⟩ :=
  of_check (by decide +kernel)

theorem s24016_1 : Run get 24016 1 ⟨278109489,278109495⟩ :=
  of_check (by decide +kernel)

theorem s23984_16 : Run get 23984 16 ⟨276160707,277074568⟩ :=
  of_check (by decide +kernel)

theorem s24000_64 : Run get 24000 64 ⟨277135464,280966115⟩ :=
  of_check (by decide +kernel)

theorem s24016_16 : Run get 24016 16 ⟨278109489,279021947⟩ :=
  of_check (by decide +kernel)

theorem s24032_32 : Run get 24032 32 ⟨279082746,280966115⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
