import Point22AtlasRangeGroup311Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf311

private abbrev get := fastBlock verifiedRow 3 1 .first
private theorem get_eq_raw : get = rawBlock verifiedRow 3 1 .first :=
  funext (fastBlock_eq_raw verifiedRow 3 1 .first)

private theorem s512_512 : Run get 512 512 ⟨-133400194948,-65665465339⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨-196846817962,-133529118206⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨-253886501005,-196965063292⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-253886501005,-133529118206⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

theorem claim818 : CheckedClaim verifiedRow ⟨3,1,1,96,2084,-257714040712,-8798009078⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 96 1989 ⟨-257713985780,-8798064010⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_32 (by decide)) (append (widen s2080_4 (by decide)) (widen s2084_1 (by decide)))))))))

private theorem s2048_512 : Run get 2048 512 ⟨-302882006377,-253990503758⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨-342618751383,-302968962285⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-342618751383,-253990503758⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-372350388304,-342686736861⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim819 : CheckedClaim verifiedRow ⟨3,1,1,96,4072,-391156497394,-8798009078⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 96 3977 ⟨-391156442462,-8798064010⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide))))))))))))))

theorem claim820 : CheckedClaim verifiedRow ⟨3,1,1,2084,4072,-391156497394,-257713930839⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 2084 1989 ⟨-391156442462,-257713985771⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨-391811490198,-372398417432⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-391811490198,-342686736861⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

theorem claim821 : CheckedClaim verifiedRow ⟨3,1,1,2116,4104,-392062313031,-260989746770⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 2116 1989 ⟨-392062258099,-260989801702⟩
  rw [← get_eq_raw]
  exact (append (widen s2116_4 (by decide)) (append (widen s2120_8 (by decide)) (append (widen s2128_16 (by decide)) (append (widen s2144_32 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_8 (by decide)) (widen s4104_1 (by decide)))))))))))

private theorem s4096_512 : Run get 4096 512 ⟨-401198326481,-391839507499⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

theorem claim822 : CheckedClaim verifiedRow ⟨3,1,1,4072,5066,-402291092126,-391156387521⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 4072 995 ⟨-402291037194,-391156442453⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_64 (by decide)) (append (widen s5056_8 (by decide)) (append (widen s5064_2 (by decide)) (widen s5066_1 (by decide))))))))))

private theorem s4608_512 : Run get 4608 512 ⟨-402291037194,-401121388822⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-402291037194,-391839507499⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨-401112553861,-392535466384⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim823 : CheckedClaim verifiedRow ⟨3,1,1,4072,6060,-402291092126,-379668259584⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 4072 1989 ⟨-402291037194,-379668314516⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨-392511130601,-376654481891⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨-401112553861,-376654481891⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-402291037194,-376654481891⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨-376617209775,-354858899131⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨-354811488786,-328603311021⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨-376617209775,-328603311021⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨-328548618449,-299330921268⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim824 : CheckedClaim verifiedRow ⟨3,1,1,4072,8048,-402291092126,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 4072 3977 ⟨-402291037194,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim825 : CheckedClaim verifiedRow ⟨3,1,1,4104,8080,-402291092126,-275182671141⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 4104 3977 ⟨-402291037194,-275182726073⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

theorem claim826 : CheckedClaim verifiedRow ⟨3,1,1,4136,8112,-402291092126,-273230093223⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 4136 3977 ⟨-402291037194,-273230148155⟩
  rw [← get_eq_raw]
  exact (append (widen s4136_8 (by decide)) (append (widen s4144_16 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide)))))))))))))))

theorem claim827 : CheckedClaim verifiedRow ⟨3,1,1,5066,6060,-401542926429,-379668259584⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 5066 995 ⟨-401542871497,-379668314516⟩
  rw [← get_eq_raw]
  exact (append (widen s5066_2 (by decide)) (append (widen s5068_4 (by decide)) (append (widen s5072_16 (by decide)) (append (widen s5088_32 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide))))))))))))

theorem claim828 : CheckedClaim verifiedRow ⟨3,1,1,6060,7054,-379668369457,-334707023749⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 6060 995 ⟨-379668314525,-334707078681⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_128 (by decide)) (append (widen s7040_8 (by decide)) (append (widen s7048_4 (by decide)) (append (widen s7052_2 (by decide)) (widen s7054_1 (by decide)))))))))))

theorem claim829 : CheckedClaim verifiedRow ⟨3,1,1,6060,8048,-379668369457,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 6060 1989 ⟨-379668314525,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim830 : CheckedClaim verifiedRow ⟨3,1,1,7054,7551,-334707133622,-306855447591⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7054 498 ⟨-334707078690,-306855502523⟩
  rw [← get_eq_raw]
  exact (append (widen s7054_2 (by decide)) (append (widen s7056_16 (by decide)) (append (widen s7072_32 (by decide)) (append (widen s7104_64 (by decide)) (append (widen s7168_256 (by decide)) (widen s7424_128 (by decide)))))))

theorem claim831 : CheckedClaim verifiedRow ⟨3,1,1,7054,8048,-334707133622,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7054 995 ⟨-334707078690,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s7054_2 (by decide)) (append (widen s7056_16 (by decide)) (append (widen s7072_32 (by decide)) (append (widen s7104_64 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim832 : CheckedClaim verifiedRow ⟨3,1,1,7551,7799,-306855557464,-292182700592⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7551 249 ⟨-306855502532,-292182755524⟩
  rw [← get_eq_raw]
  exact (append (widen s7551_1 (by decide)) (append (widen s7552_128 (by decide)) (append (widen s7680_64 (by decide)) (append (widen s7744_32 (by decide)) (append (widen s7776_16 (by decide)) (widen s7792_8 (by decide)))))))

theorem claim833 : CheckedClaim verifiedRow ⟨3,1,1,7551,8048,-306855557464,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7551 498 ⟨-306855502532,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s7551_1 (by decide)) (append (widen s7552_128 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide))))))))

theorem claim834 : CheckedClaim verifiedRow ⟨3,1,1,7799,7923,-292182810465,-284718747608⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7799 125 ⟨-292182755533,-284718802540⟩
  rw [← get_eq_raw]
  exact (append (widen s7799_1 (by decide)) (append (widen s7800_8 (by decide)) (append (widen s7808_64 (by decide)) (append (widen s7872_32 (by decide)) (append (widen s7904_16 (by decide)) (widen s7920_4 (by decide)))))))

theorem claim835 : CheckedClaim verifiedRow ⟨3,1,1,7799,8048,-292182810465,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7799 250 ⟨-292182755533,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s7799_1 (by decide)) (append (widen s7800_8 (by decide)) (append (widen s7808_128 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide))))))))

theorem claim836 : CheckedClaim verifiedRow ⟨3,1,1,7923,7985,-284718857481,-280962700855⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7923 63 ⟨-284718802549,-280962755787⟩
  rw [← get_eq_raw]
  exact (append (widen s7923_1 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_2 (by decide)))))))

theorem claim837 : CheckedClaim verifiedRow ⟨3,1,1,7923,8048,-284718857481,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7923 126 ⟨-284718802549,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s7923_1 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide))))))))

theorem claim838 : CheckedClaim verifiedRow ⟨3,1,1,7985,8000,-280962810728,-280051921881⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7985 16 ⟨-280962755796,-280051976813⟩
  rw [← get_eq_raw]
  exact (append (widen s7985_1 (by decide)) (append (widen s7986_2 (by decide)) (append (widen s7988_4 (by decide)) (append (widen s7992_8 (by decide)) (widen s8000_1 (by decide))))))

theorem claim839 : CheckedClaim verifiedRow ⟨3,1,1,7985,8016,-280962810728,-279079609609⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7985 32 ⟨-280962755796,-279079664541⟩
  rw [← get_eq_raw]
  exact (append (widen s7985_1 (by decide)) (append (widen s7986_2 (by decide)) (append (widen s7988_4 (by decide)) (append (widen s7992_8 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))

theorem claim840 : CheckedClaim verifiedRow ⟨3,1,1,7985,8048,-280962810728,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 7985 64 ⟨-280962755796,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s7985_1 (by decide)) (append (widen s7986_2 (by decide)) (append (widen s7988_4 (by decide)) (append (widen s7992_8 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide))))))))

theorem claim841 : CheckedClaim verifiedRow ⟨3,1,1,8000,8016,-280052031754,-279079609609⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8000 17 ⟨-280051976822,-279079664541⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))

theorem claim842 : CheckedClaim verifiedRow ⟨3,1,1,8016,8024,-279079719482,-278593149242⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8016 9 ⟨-279079664550,-278593204174⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_8 (by decide)) (widen s8024_1 (by decide)))

theorem claim843 : CheckedClaim verifiedRow ⟨3,1,1,8016,8032,-279079719482,-278106492121⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8016 17 ⟨-279079664550,-278106547053⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (widen s8032_1 (by decide)))

theorem claim844 : CheckedClaim verifiedRow ⟨3,1,1,8016,8048,-279079719482,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8016 33 ⟨-279079664550,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide))))

theorem claim845 : CheckedClaim verifiedRow ⟨3,1,1,8024,8026,-278593259115,-278471503230⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8024 3 ⟨-278593204183,-278471558162⟩
  rw [← get_eq_raw]
  exact (append (widen s8024_2 (by decide)) (widen s8026_1 (by decide)))

theorem claim846 : CheckedClaim verifiedRow ⟨3,1,1,8024,8028,-278593259115,-278349844991⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8024 5 ⟨-278593204183,-278349899923⟩
  rw [← get_eq_raw]
  exact (append (widen s8024_4 (by decide)) (widen s8028_1 (by decide)))

theorem claim847 : CheckedClaim verifiedRow ⟨3,1,1,8024,8032,-278593259115,-278106492121⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8024 9 ⟨-278593204183,-278106547053⟩
  rw [← get_eq_raw]
  exact (append (widen s8024_8 (by decide)) (widen s8032_1 (by decide)))

theorem claim848 : CheckedClaim verifiedRow ⟨3,1,1,8028,8030,-278349954864,-278228174599⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8028 3 ⟨-278349899932,-278228229531⟩
  rw [← get_eq_raw]
  exact (append (widen s8028_2 (by decide)) (widen s8030_1 (by decide)))

theorem claim849 : CheckedClaim verifiedRow ⟨3,1,1,8028,8032,-278349954864,-278106492121⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8028 5 ⟨-278349899932,-278106547053⟩
  rw [← get_eq_raw]
  exact (append (widen s8028_4 (by decide)) (widen s8032_1 (by decide)))

theorem claim850 : CheckedClaim verifiedRow ⟨3,1,1,8030,8032,-278228284472,-278106492121⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8030 3 ⟨-278228229540,-278106547053⟩
  rw [← get_eq_raw]
  exact (append (widen s8030_2 (by decide)) (widen s8032_1 (by decide)))

theorem claim851 : CheckedClaim verifiedRow ⟨3,1,1,8032,8033,-278106601994,-278045646374⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8032 2 ⟨-278106547062,-278045701306⟩
  rw [← get_eq_raw]
  exact (widen s8032_2 (by decide))

theorem claim852 : CheckedClaim verifiedRow ⟨3,1,1,8032,8034,-278106601994,-277984797632⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8032 3 ⟨-278106547062,-277984852564⟩
  rw [← get_eq_raw]
  exact (append (widen s8032_2 (by decide)) (widen s8034_1 (by decide)))

theorem claim853 : CheckedClaim verifiedRow ⟨3,1,1,8032,8036,-278106601994,-277863091200⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8032 5 ⟨-278106547062,-277863146132⟩
  rw [← get_eq_raw]
  exact (append (widen s8032_4 (by decide)) (widen s8036_1 (by decide)))

theorem claim854 : CheckedClaim verifiedRow ⟨3,1,1,8032,8040,-278106601994,-277619642792⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8032 9 ⟨-278106547062,-277619697724⟩
  rw [← get_eq_raw]
  exact (append (widen s8032_8 (by decide)) (widen s8040_1 (by decide)))

theorem claim855 : CheckedClaim verifiedRow ⟨3,1,1,8032,8048,-278106601994,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8032 17 ⟨-278106547062,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))

theorem claim856 : CheckedClaim verifiedRow ⟨3,1,1,8033,8034,-278045756247,-277984797632⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8033 2 ⟨-278045701315,-277984852564⟩
  rw [← get_eq_raw]
  exact (append (widen s8033_1 (by decide)) (widen s8034_1 (by decide)))

theorem claim857 : CheckedClaim verifiedRow ⟨3,1,1,8034,8036,-277984907505,-277863091200⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8034 3 ⟨-277984852573,-277863146132⟩
  rw [← get_eq_raw]
  exact (append (widen s8034_2 (by decide)) (widen s8036_1 (by decide)))

theorem claim858 : CheckedClaim verifiedRow ⟨3,1,1,8036,8040,-277863201073,-277619642792⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8036 5 ⟨-277863146141,-277619697724⟩
  rw [← get_eq_raw]
  exact (append (widen s8036_4 (by decide)) (widen s8040_1 (by decide)))

theorem claim859 : CheckedClaim verifiedRow ⟨3,1,1,8040,8048,-277619752665,-277132605779⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8040 9 ⟨-277619697733,-277132660711⟩
  rw [← get_eq_raw]
  exact (append (widen s8040_8 (by decide)) (widen s8048_1 (by decide)))

theorem claim860 : CheckedClaim verifiedRow ⟨3,1,1,8048,8063,-277132715652,-276218921247⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 16 ⟨-277132660720,-276218976179⟩
  rw [← get_eq_raw]
  exact (widen s8048_16 (by decide))

theorem claim861 : CheckedClaim verifiedRow ⟨3,1,1,8048,8079,-277132715652,-275243648098⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 32 ⟨-277132660720,-275243703030⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (widen s8064_16 (by decide)))

theorem claim862 : CheckedClaim verifiedRow ⟨3,1,1,8048,8110,-277132715652,-273352201380⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 63 ⟨-277132660720,-273352256312⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (append (widen s8108_2 (by decide)) (widen s8110_1 (by decide)))))))

theorem claim863 : CheckedClaim verifiedRow ⟨3,1,1,8048,8172,-277132715652,-269562874639⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 125 ⟨-277132660720,-269562929571⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_64 (by decide)) (append (widen s8128_32 (by decide)) (append (widen s8160_8 (by decide)) (append (widen s8168_4 (by decide)) (widen s8172_1 (by decide)))))))

theorem claim864 : CheckedClaim verifiedRow ⟨3,1,1,8048,8296,-277132715652,-261965587423⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 249 ⟨-277132660720,-261965642355⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_64 (by decide)) (append (widen s8256_32 (by decide)) (append (widen s8288_8 (by decide)) (widen s8296_1 (by decide)))))))

theorem claim865 : CheckedClaim verifiedRow ⟨3,1,1,8048,8545,-277132715652,-246689870658⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 498 ⟨-277132660720,-246689925590⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_256 (by decide)) (append (widen s8448_64 (by decide)) (append (widen s8512_32 (by decide)) (widen s8544_2 (by decide)))))))

private theorem s8192_512 : Run get 8192 512 ⟨-268339001344,-237027373407⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

theorem claim866 : CheckedClaim verifiedRow ⟨3,1,1,8048,9042,-277132715652,-216524880124⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 995 ⟨-277132660720,-216524935056⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_64 (by decide)) (append (widen s9024_16 (by decide)) (append (widen s9040_2 (by decide)) (widen s9042_1 (by decide)))))))))

private theorem s8704_512 : Run get 8704 512 ⟨-236966373219,-206246202340⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨-268339001344,-206246202340⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨-206187237513,-176885557330⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

theorem claim867 : CheckedClaim verifiedRow ⟨3,1,1,8048,10036,-277132715652,-160121197853⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 1989 ⟨-277132660720,-160121252785⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))

private theorem s9728_512 : Run get 9728 512 ⟨-176830039566,-149562889522⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨-206187237513,-149562889522⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨-268339001344,-149562889522⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨-149511820670,-124691382688⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨-124645379983,-102497520826⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨-149511820670,-102497520826⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨-102456859174,-83045654841⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim868 : CheckedClaim verifiedRow ⟨3,1,1,8048,12024,-277132715652,-74560162022⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8048 3977 ⟨-277132660720,-74560216954⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim869 : CheckedClaim verifiedRow ⟨3,1,1,8063,8079,-276219031120,-275243648098⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8063 17 ⟨-276218976188,-275243703030⟩
  rw [← get_eq_raw]
  exact (append (widen s8063_1 (by decide)) (widen s8064_16 (by decide)))

theorem claim870 : CheckedClaim verifiedRow ⟨3,1,1,8079,8110,-275243757971,-273352201380⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8079 32 ⟨-275243703039,-273352256312⟩
  rw [← get_eq_raw]
  exact (append (widen s8079_1 (by decide)) (append (widen s8080_16 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (append (widen s8108_2 (by decide)) (widen s8110_1 (by decide)))))))

theorem claim871 : CheckedClaim verifiedRow ⟨3,1,1,8080,10068,-275182781014,-158431944518⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8080 1989 ⟨-275182726082,-158431999450⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))

theorem claim872 : CheckedClaim verifiedRow ⟨3,1,1,8080,12056,-275182781014,-73514768175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8080 3977 ⟨-275182726082,-73514823107⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

private theorem s11776_512 : Run get 11776 512 ⟨-83010319430,-66266234735⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨-102456859174,-66266234735⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨-149511820670,-66266234735⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨-268339001344,-66266234735⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨-66235977741,-51984750059⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨-51959146206,-39948987452⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨-66235977741,-39948987452⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨-39927484356,-29852879930⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨-29834840561,-21355910098⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨-39927484356,-21355910098⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨-66235977741,-21355910098⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨-21340645974,-14097677212⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨-14084472148,-7707804752⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨-21340645974,-7707804752⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨-7695930008,-1811827940⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim873 : CheckedClaim verifiedRow ⟨3,1,1,8080,16032,-275182781014,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8080 7953 ⟨-275182726082,5⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim874 : CheckedClaim verifiedRow ⟨3,1,1,8110,8172,-273352311253,-269562874639⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8110 63 ⟨-273352256321,-269562929571⟩
  rw [← get_eq_raw]
  exact (append (widen s8110_2 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_32 (by decide)) (append (widen s8160_8 (by decide)) (append (widen s8168_4 (by decide)) (widen s8172_1 (by decide)))))))

theorem claim875 : CheckedClaim verifiedRow ⟨3,1,1,8112,12088,-273230203096,-72479512110⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8112 3977 ⟨-273230148164,-72479567042⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_32 (by decide)) (append (widen s12064_16 (by decide)) (append (widen s12080_8 (by decide)) (widen s12088_1 (by decide)))))))))))

theorem claim876 : CheckedClaim verifiedRow ⟨3,1,1,8112,16064,-273230203096,359797899⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8112 7953 ⟨-273230148164,359742967⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim877 : CheckedClaim verifiedRow ⟨3,1,1,8172,8296,-269562984512,-261965587423⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8172 125 ⟨-269562929580,-261965642355⟩
  rw [← get_eq_raw]
  exact (append (widen s8172_4 (by decide)) (append (widen s8176_16 (by decide)) (append (widen s8192_64 (by decide)) (append (widen s8256_32 (by decide)) (append (widen s8288_8 (by decide)) (widen s8296_1 (by decide)))))))

theorem claim878 : CheckedClaim verifiedRow ⟨3,1,1,8296,8545,-261965697296,-246689870658⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8296 250 ⟨-261965642364,-246689925590⟩
  rw [← get_eq_raw]
  exact (append (widen s8296_8 (by decide)) (append (widen s8304_16 (by decide)) (append (widen s8320_128 (by decide)) (append (widen s8448_64 (by decide)) (append (widen s8512_32 (by decide)) (widen s8544_2 (by decide)))))))

theorem claim879 : CheckedClaim verifiedRow ⟨3,1,1,8545,9042,-246689980531,-216524880124⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 8545 498 ⟨-246689925599,-216524935056⟩
  rw [← get_eq_raw]
  exact (append (widen s8545_1 (by decide)) (append (widen s8546_2 (by decide)) (append (widen s8548_4 (by decide)) (append (widen s8552_8 (by decide)) (append (widen s8560_16 (by decide)) (append (widen s8576_128 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_64 (by decide)) (append (widen s9024_16 (by decide)) (append (widen s9040_2 (by decide)) (widen s9042_1 (by decide))))))))))))

theorem claim880 : CheckedClaim verifiedRow ⟨3,1,1,9042,10036,-216524989997,-160121197853⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 9042 995 ⟨-216524935065,-160121252785⟩
  rw [← get_eq_raw]
  exact (append (widen s9042_2 (by decide)) (append (widen s9044_4 (by decide)) (append (widen s9048_8 (by decide)) (append (widen s9056_32 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))))

theorem claim881 : CheckedClaim verifiedRow ⟨3,1,1,10036,11030,-160121307726,-112257851948⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 10036 995 ⟨-160121252794,-112257906880⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_16 (by decide)) (append (widen s11024_4 (by decide)) (append (widen s11028_2 (by decide)) (widen s11030_1 (by decide)))))))))))

theorem claim882 : CheckedClaim verifiedRow ⟨3,1,1,10036,12024,-160121307726,-74560162022⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 10036 1989 ⟨-160121252794,-74560216954⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim883 : CheckedClaim verifiedRow ⟨3,1,1,10068,11062,-158432054391,-110883635251⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 10068 995 ⟨-158431999459,-110883690183⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_32 (by decide)) (append (widen s11040_16 (by decide)) (append (widen s11056_4 (by decide)) (append (widen s11060_2 (by decide)) (widen s11062_1 (by decide))))))))))))

theorem claim884 : CheckedClaim verifiedRow ⟨3,1,1,10068,12056,-158432054391,-73514768175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 10068 1989 ⟨-158431999459,-73514823107⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim885 : CheckedClaim verifiedRow ⟨3,1,1,10533,11030,-134963081848,-112257851948⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 10533 498 ⟨-134963026916,-112257906880⟩
  rw [← get_eq_raw]
  exact (append (widen s10533_1 (by decide)) (append (widen s10534_2 (by decide)) (append (widen s10536_8 (by decide)) (append (widen s10544_16 (by decide)) (append (widen s10560_64 (by decide)) (append (widen s10624_128 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_16 (by decide)) (append (widen s11024_4 (by decide)) (append (widen s11028_2 (by decide)) (widen s11030_1 (by decide))))))))))))

theorem claim886 : CheckedClaim verifiedRow ⟨3,1,1,11030,12024,-112257961821,-74560162022⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 11030 995 ⟨-112257906889,-74560216954⟩
  rw [← get_eq_raw]
  exact (append (widen s11030_2 (by decide)) (append (widen s11032_8 (by decide)) (append (widen s11040_32 (by decide)) (append (widen s11072_64 (by decide)) (append (widen s11136_128 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim887 : CheckedClaim verifiedRow ⟨3,1,1,11062,12056,-110883745124,-73514768175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 11062 995 ⟨-110883690192,-73514823107⟩
  rw [← get_eq_raw]
  exact (append (widen s11062_2 (by decide)) (append (widen s11064_8 (by decide)) (append (widen s11072_64 (by decide)) (append (widen s11136_128 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide))))))))))

theorem claim888 : CheckedClaim verifiedRow ⟨3,1,1,12024,14012,-74560271895,-26548890580⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12024 1989 ⟨-74560216963,-26548945512⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim889 : CheckedClaim verifiedRow ⟨3,1,1,12024,16000,-74560271895,-359688025⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12024 3977 ⟨-74560216963,-359742957⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim890 : CheckedClaim verifiedRow ⟨3,1,1,12056,13050,-73514878048,-45821727833⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12056 995 ⟨-73514823116,-45821782765⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_32 (by decide)) (append (widen s13024_16 (by decide)) (append (widen s13040_8 (by decide)) (append (widen s13048_2 (by decide)) (widen s13050_1 (by decide)))))))))))))

theorem claim891 : CheckedClaim verifiedRow ⟨3,1,1,12056,14044,-73514878048,-26009803894⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12056 1989 ⟨-73514823116,-26009858826⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim892 : CheckedClaim verifiedRow ⟨3,1,1,12056,16032,-73514878048,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12056 3977 ⟨-73514823116,5⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim893 : CheckedClaim verifiedRow ⟨3,1,1,12088,16064,-72479621983,359797899⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 12088 3977 ⟨-72479567051,359742967⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim894 : CheckedClaim verifiedRow ⟨3,1,1,13018,14012,-46578677015,-26548890580⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 13018 995 ⟨-46578622083,-26548945512⟩
  rw [← get_eq_raw]
  exact (append (widen s13018_2 (by decide)) (append (widen s13020_4 (by decide)) (append (widen s13024_32 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide))))))))))))

theorem claim895 : CheckedClaim verifiedRow ⟨3,1,1,13050,14044,-45821837706,-26009803894⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 13050 995 ⟨-45821782774,-26009858826⟩
  rw [← get_eq_raw]
  exact (append (widen s13050_2 (by decide)) (append (widen s13052_4 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))

theorem claim896 : CheckedClaim verifiedRow ⟨3,1,1,14012,16000,-26549000453,-359688025⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 14012 1989 ⟨-26548945521,-359742957⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim897 : CheckedClaim verifiedRow ⟨3,1,1,14044,15038,-26009913767,-11632346848⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 14044 995 ⟨-26009858835,-11632401780⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_128 (by decide)) (append (widen s14976_32 (by decide)) (append (widen s15008_16 (by decide)) (append (widen s15024_8 (by decide)) (append (widen s15032_4 (by decide)) (append (widen s15036_2 (by decide)) (widen s15038_1 (by decide))))))))))))

theorem claim898 : CheckedClaim verifiedRow ⟨3,1,1,14044,16032,-26009913767,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 14044 1989 ⟨-26009858835,5⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

theorem claim899 : CheckedClaim verifiedRow ⟨3,1,1,15038,15535,-11632456721,-5644270358⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15038 498 ⟨-11632401789,-5644325290⟩
  rw [← get_eq_raw]
  exact (append (widen s15038_2 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_128 (by decide)) (append (widen s15488_32 (by decide)) (widen s15520_16 (by decide)))))))

theorem claim900 : CheckedClaim verifiedRow ⟨3,1,1,15038,16032,-11632456721,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15038 995 ⟨-11632401789,5⟩
  rw [← get_eq_raw]
  exact (append (widen s15038_2 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))

theorem claim901 : CheckedClaim verifiedRow ⟨3,1,1,15535,15783,-5644380231,-2806282639⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15535 249 ⟨-5644325299,-2806337571⟩
  rw [← get_eq_raw]
  exact (append (widen s15535_1 (by decide)) (append (widen s15536_16 (by decide)) (append (widen s15552_64 (by decide)) (append (widen s15616_128 (by decide)) (append (widen s15744_32 (by decide)) (widen s15776_8 (by decide)))))))

theorem claim902 : CheckedClaim verifiedRow ⟨3,1,1,15535,16032,-5644380231,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15535 498 ⟨-5644325299,5⟩
  rw [← get_eq_raw]
  exact (append (widen s15535_1 (by decide)) (append (widen s15536_16 (by decide)) (append (widen s15552_64 (by decide)) (append (widen s15616_256 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))

theorem claim903 : CheckedClaim verifiedRow ⟨3,1,1,15783,15907,-2806392512,-1406042995⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15783 125 ⟨-2806337580,-1406097927⟩
  rw [← get_eq_raw]
  exact (append (widen s15783_1 (by decide)) (append (widen s15784_8 (by decide)) (append (widen s15792_16 (by decide)) (append (widen s15808_64 (by decide)) (append (widen s15872_32 (by decide)) (widen s15904_4 (by decide)))))))

theorem claim904 : CheckedClaim verifiedRow ⟨3,1,1,15783,16032,-2806392512,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15783 250 ⟨-2806337580,5⟩
  rw [← get_eq_raw]
  exact (append (widen s15783_1 (by decide)) (append (widen s15784_8 (by decide)) (append (widen s15792_16 (by decide)) (append (widen s15808_64 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))

theorem claim905 : CheckedClaim verifiedRow ⟨3,1,1,15907,15969,-1406152868,-708275630⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15907 63 ⟨-1406097936,-708330562⟩
  rw [← get_eq_raw]
  exact (append (widen s15907_1 (by decide)) (append (widen s15908_4 (by decide)) (append (widen s15912_8 (by decide)) (append (widen s15920_16 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_2 (by decide)))))))

theorem claim906 : CheckedClaim verifiedRow ⟨3,1,1,15907,16032,-1406152868,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15907 126 ⟨-1406097936,5⟩
  rw [← get_eq_raw]
  exact (append (widen s15907_1 (by decide)) (append (widen s15908_4 (by decide)) (append (widen s15912_8 (by decide)) (append (widen s15920_16 (by decide)) (append (widen s15936_64 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))

theorem claim907 : CheckedClaim verifiedRow ⟨3,1,1,15969,16000,-708385503,-359688025⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15969 32 ⟨-708330571,-359742957⟩
  rw [← get_eq_raw]
  exact (append (widen s15969_1 (by decide)) (append (widen s15970_2 (by decide)) (append (widen s15972_4 (by decide)) (append (widen s15976_8 (by decide)) (append (widen s15984_16 (by decide)) (widen s16000_1 (by decide)))))))

theorem claim908 : CheckedClaim verifiedRow ⟨3,1,1,15969,16032,-708385503,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 15969 64 ⟨-708330571,5⟩
  rw [← get_eq_raw]
  exact (append (widen s15969_1 (by decide)) (append (widen s15970_2 (by decide)) (append (widen s15972_4 (by decide)) (append (widen s15976_8 (by decide)) (append (widen s15984_16 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))

theorem claim909 : CheckedClaim verifiedRow ⟨3,1,1,16000,16016,-359797899,-179810808⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16000 17 ⟨-359742967,-179865740⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_16 (by decide)) (widen s16016_1 (by decide)))

theorem claim910 : CheckedClaim verifiedRow ⟨3,1,1,16000,16032,-359797899,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16000 33 ⟨-359742967,5⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))

private theorem s16384_512 : Run get 16384 512 ⟨3977363513,10001396999⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨10013682404,16669945601⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨3977363513,16669945601⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨16683834001,24345012772⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

private theorem s17920_512 : Run get 17920 512 ⟨24361229510,33394156110⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨16683834001,33394156110⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨3977363513,33394156110⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨33413409240,44171792780⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨44194754864,57007615178⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨33413409240,57007615178⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

private theorem s19456_512 : Run get 19456 512 ⟨57034896062,72190221705⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim911 : CheckedClaim verifiedRow ⟨3,1,1,16000,19976,-359797899,72479621983⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16000 3977 ⟨-359742967,72479567051⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim912 : CheckedClaim verifiedRow ⟨3,1,1,16016,16024,-179920681,-89877219⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16016 9 ⟨-179865749,-89932151⟩
  rw [← get_eq_raw]
  exact (append (widen s16016_8 (by decide)) (widen s16024_1 (by decide)))

theorem claim913 : CheckedClaim verifiedRow ⟨3,1,1,16016,16032,-179920681,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16016 17 ⟨-179865749,5⟩
  rw [← get_eq_raw]
  exact (append (widen s16016_16 (by decide)) (widen s16032_1 (by decide)))

theorem claim914 : CheckedClaim verifiedRow ⟨3,1,1,16024,16028,-89987092,-44911052⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16024 5 ⟨-89932160,-44965984⟩
  rw [← get_eq_raw]
  exact (append (widen s16024_4 (by decide)) (widen s16028_1 (by decide)))

theorem claim915 : CheckedClaim verifiedRow ⟨3,1,1,16024,16032,-89987092,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16024 9 ⟨-89932160,5⟩
  rw [← get_eq_raw]
  exact (append (widen s16024_8 (by decide)) (widen s16032_1 (by decide)))

theorem claim916 : CheckedClaim verifiedRow ⟨3,1,1,16026,16028,-67503975,-44911052⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16026 3 ⟨-67449043,-44965984⟩
  rw [← get_eq_raw]
  exact (append (widen s16026_2 (by decide)) (widen s16028_1 (by decide)))

theorem claim917 : CheckedClaim verifiedRow ⟨3,1,1,16028,16030,-45020925,-22428047⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16028 3 ⟨-44965993,-22482979⟩
  rw [← get_eq_raw]
  exact (append (widen s16028_2 (by decide)) (widen s16030_1 (by decide)))

theorem claim918 : CheckedClaim verifiedRow ⟨3,1,1,16028,16032,-45020925,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16028 5 ⟨-44965993,5⟩
  rw [← get_eq_raw]
  exact (append (widen s16028_4 (by decide)) (widen s16032_1 (by decide)))

theorem claim919 : CheckedClaim verifiedRow ⟨3,1,1,16030,16032,-22537920,54937⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16030 3 ⟨-22482988,5⟩
  rw [← get_eq_raw]
  exact (append (widen s16030_2 (by decide)) (widen s16032_1 (by decide)))

theorem claim920 : CheckedClaim verifiedRow ⟨3,1,1,16032,16035,-54937,33779418⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 4 ⟨-5,33724486⟩
  rw [← get_eq_raw]
  exact (widen s16032_4 (by decide))

theorem claim921 : CheckedClaim verifiedRow ⟨3,1,1,16032,16039,-54937,78745523⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 8 ⟨-5,78690591⟩
  rw [← get_eq_raw]
  exact (widen s16032_8 (by decide))

theorem claim922 : CheckedClaim verifiedRow ⟨3,1,1,16032,16047,-54937,168678855⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 16 ⟨-5,168623923⟩
  rw [← get_eq_raw]
  exact (widen s16032_16 (by decide))

theorem claim923 : CheckedClaim verifiedRow ⟨3,1,1,16032,16063,-54937,348555020⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 32 ⟨-5,348500088⟩
  rw [← get_eq_raw]
  exact (widen s16032_32 (by decide))

theorem claim924 : CheckedClaim verifiedRow ⟨3,1,1,16032,16094,-54937,697138543⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 63 ⟨-5,697083611⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_16 (by decide)) (append (widen s16080_8 (by decide)) (append (widen s16088_4 (by decide)) (append (widen s16092_2 (by decide)) (widen s16094_1 (by decide)))))))

theorem claim925 : CheckedClaim verifiedRow ⟨3,1,1,16032,16156,-54937,1394889672⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 125 ⟨-5,1394834740⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_16 (by decide)) (append (widen s16144_8 (by decide)) (append (widen s16152_4 (by decide)) (widen s16156_1 (by decide)))))))

theorem claim926 : CheckedClaim verifiedRow ⟨3,1,1,16032,16280,-54937,2795064544⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 249 ⟨-5,2795009612⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_128 (by decide)) (append (widen s16256_16 (by decide)) (append (widen s16272_8 (by decide)) (widen s16280_1 (by decide)))))))

theorem claim927 : CheckedClaim verifiedRow ⟨3,1,1,16032,16529,-54937,5644380231⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 498 ⟨-5,5644325299⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_128 (by decide)) (append (widen s16512_16 (by decide)) (widen s16528_2 (by decide)))))))

theorem claim928 : CheckedClaim verifiedRow ⟨3,1,1,16032,17026,-54937,11632456721⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 995 ⟨-5,11632401789⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_128 (by decide)) (append (widen s17024_2 (by decide)) (widen s17026_1 (by decide))))))))

theorem claim929 : CheckedClaim verifiedRow ⟨3,1,1,16032,18020,-54937,26009913767⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 1989 ⟨-5,26009858835⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim930 : CheckedClaim verifiedRow ⟨3,1,1,16032,20008,-54937,73514878048⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16032 3977 ⟨-5,73514823116⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

theorem claim931 : CheckedClaim verifiedRow ⟨3,1,1,16034,16035,22428047,33779418⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16034 2 ⟨22482979,33724486⟩
  rw [← get_eq_raw]
  exact (widen s16034_2 (by decide))

theorem claim932 : CheckedClaim verifiedRow ⟨3,1,1,16035,16037,33669545,56262443⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16035 3 ⟨33724477,56207511⟩
  rw [← get_eq_raw]
  exact (append (widen s16035_1 (by decide)) (widen s16036_2 (by decide)))

theorem claim933 : CheckedClaim verifiedRow ⟨3,1,1,16037,16039,56152570,78745523⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16037 3 ⟨56207502,78690591⟩
  rw [← get_eq_raw]
  exact (append (widen s16037_1 (by decide)) (widen s16038_2 (by decide)))

theorem claim934 : CheckedClaim verifiedRow ⟨3,1,1,16039,16047,78635650,168678855⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16039 9 ⟨78690582,168623923⟩
  rw [← get_eq_raw]
  exact (append (widen s16039_1 (by decide)) (widen s16040_8 (by decide)))

theorem claim935 : CheckedClaim verifiedRow ⟨3,1,1,16047,16063,168568982,348555020⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16047 17 ⟨168623914,348500088⟩
  rw [← get_eq_raw]
  exact (append (widen s16047_1 (by decide)) (widen s16048_16 (by decide)))

theorem claim936 : CheckedClaim verifiedRow ⟨3,1,1,16063,16094,348445147,697138543⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16063 32 ⟨348500079,697083611⟩
  rw [← get_eq_raw]
  exact (append (widen s16063_1 (by decide)) (append (widen s16064_16 (by decide)) (append (widen s16080_8 (by decide)) (append (widen s16088_4 (by decide)) (append (widen s16092_2 (by decide)) (widen s16094_1 (by decide)))))))

theorem claim937 : CheckedClaim verifiedRow ⟨3,1,1,16064,18052,359688025,26549000453⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16064 1989 ⟨359742957,26548945521⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_128 (by decide)) (append (widen s18048_4 (by decide)) (widen s18052_1 (by decide))))))))

theorem claim938 : CheckedClaim verifiedRow ⟨3,1,1,16064,20040,359688025,74560271895⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16064 3977 ⟨359742957,74560216963⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim939 : CheckedClaim verifiedRow ⟨3,1,1,16094,16156,697028670,1394889672⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16094 63 ⟨697083602,1394834740⟩
  rw [← get_eq_raw]
  exact (append (widen s16094_2 (by decide)) (append (widen s16096_32 (by decide)) (append (widen s16128_16 (by decide)) (append (widen s16144_8 (by decide)) (append (widen s16152_4 (by decide)) (widen s16156_1 (by decide)))))))

theorem claim940 : CheckedClaim verifiedRow ⟨3,1,1,16156,16280,1394779799,2795064544⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16156 125 ⟨1394834731,2795009612⟩
  rw [← get_eq_raw]
  exact (append (widen s16156_4 (by decide)) (append (widen s16160_32 (by decide)) (append (widen s16192_64 (by decide)) (append (widen s16256_16 (by decide)) (append (widen s16272_8 (by decide)) (widen s16280_1 (by decide)))))))

theorem claim941 : CheckedClaim verifiedRow ⟨3,1,1,16280,16404,2794954671,4205919416⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16280 125 ⟨2795009603,4205864484⟩
  rw [← get_eq_raw]
  exact (append (widen s16280_8 (by decide)) (append (widen s16288_32 (by decide)) (append (widen s16320_64 (by decide)) (append (widen s16384_16 (by decide)) (append (widen s16400_4 (by decide)) (widen s16404_1 (by decide)))))))

theorem claim942 : CheckedClaim verifiedRow ⟨3,1,1,16280,16529,2794954671,5644380231⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16280 250 ⟨2795009603,5644325299⟩
  rw [← get_eq_raw]
  exact (append (widen s16280_8 (by decide)) (append (widen s16288_32 (by decide)) (append (widen s16320_64 (by decide)) (append (widen s16384_128 (by decide)) (append (widen s16512_16 (by decide)) (widen s16528_2 (by decide)))))))

theorem claim943 : CheckedClaim verifiedRow ⟨3,1,1,16404,16529,4205809543,5644380231⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16404 126 ⟨4205864475,5644325299⟩
  rw [← get_eq_raw]
  exact (append (widen s16404_4 (by decide)) (append (widen s16408_8 (by decide)) (append (widen s16416_32 (by decide)) (append (widen s16448_64 (by decide)) (append (widen s16512_16 (by decide)) (widen s16528_2 (by decide)))))))

theorem claim944 : CheckedClaim verifiedRow ⟨3,1,1,16529,17026,5644270358,11632456721⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 16529 498 ⟨5644325290,11632401789⟩
  rw [← get_eq_raw]
  exact (append (widen s16529_1 (by decide)) (append (widen s16530_2 (by decide)) (append (widen s16532_4 (by decide)) (append (widen s16536_8 (by decide)) (append (widen s16544_32 (by decide)) (append (widen s16576_64 (by decide)) (append (widen s16640_256 (by decide)) (append (widen s16896_128 (by decide)) (append (widen s17024_2 (by decide)) (widen s17026_1 (by decide)))))))))))

theorem claim945 : CheckedClaim verifiedRow ⟨3,1,1,17026,18020,11632346848,26009913767⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 17026 995 ⟨11632401780,26009858835⟩
  rw [← get_eq_raw]
  exact (append (widen s17026_2 (by decide)) (append (widen s17028_4 (by decide)) (append (widen s17032_8 (by decide)) (append (widen s17040_16 (by decide)) (append (widen s17056_32 (by decide)) (append (widen s17088_64 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide)))))))))))))

theorem claim946 : CheckedClaim verifiedRow ⟨3,1,1,18020,19014,26009803894,45821837706⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 18020 995 ⟨26009858826,45821782774⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_512 (by decide)) (append (widen s18944_64 (by decide)) (append (widen s19008_4 (by decide)) (append (widen s19012_2 (by decide)) (widen s19014_1 (by decide)))))))))))

theorem claim947 : CheckedClaim verifiedRow ⟨3,1,1,18020,20008,26009803894,73514878048⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 18020 1989 ⟨26009858826,73514823116⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim948 : CheckedClaim verifiedRow ⟨3,1,1,18052,20040,26548890580,74560271895⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 18052 1989 ⟨26548945512,74560216963⟩
  rw [← get_eq_raw]
  exact (append (widen s18052_4 (by decide)) (append (widen s18056_8 (by decide)) (append (widen s18064_16 (by decide)) (append (widen s18080_32 (by decide)) (append (widen s18112_64 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide))))))))))))

theorem claim949 : CheckedClaim verifiedRow ⟨3,1,1,19014,20008,45821727833,73514878048⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 19014 995 ⟨45821782765,73514823116⟩
  rw [← get_eq_raw]
  exact (append (widen s19014_2 (by decide)) (append (widen s19016_8 (by decide)) (append (widen s19024_16 (by decide)) (append (widen s19040_32 (by decide)) (append (widen s19072_128 (by decide)) (append (widen s19200_256 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

private theorem s20480_512 : Run get 20480 512 ⟨89983289587,110413780374⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

theorem claim950 : CheckedClaim verifiedRow ⟨3,1,1,20008,21002,73514768175,110883745124⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20008 995 ⟨73514823107,110883690192⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_512 (by decide)) (append (widen s20992_8 (by decide)) (append (widen s21000_2 (by decide)) (widen s21002_1 (by decide))))))))))

private theorem s20992_512 : Run get 20992 512 ⟨110456447043,133616865802⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨89983289587,133616865802⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

theorem claim951 : CheckedClaim verifiedRow ⟨3,1,1,20008,21996,73514768175,158432054391⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20008 1989 ⟨73514823107,158431999459⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))

private theorem s21504_512 : Run get 21504 512 ⟨133664807820,159433891920⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨159486712416,187571659910⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨133664807820,187571659910⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨89983289587,187571659910⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨187628602350,217542751002⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨217602662468,248651434309⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨187628602350,248651434309⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim952 : CheckedClaim verifiedRow ⟨3,1,1,20008,23984,73514768175,275182781014⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20008 3977 ⟨73514823107,275182726082⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim953 : CheckedClaim verifiedRow ⟨3,1,1,20040,21034,74560162022,112257961821⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20040 995 ⟨74560216954,112257906889⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_512 (by decide)) (append (widen s20992_32 (by decide)) (append (widen s21024_8 (by decide)) (append (widen s21032_2 (by decide)) (widen s21034_1 (by decide)))))))))))

theorem claim954 : CheckedClaim verifiedRow ⟨3,1,1,20040,22028,74560162022,160121307726⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20040 1989 ⟨74560216954,160121252794⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_512 (by decide)) (append (widen s22016_8 (by decide)) (append (widen s22024_4 (by decide)) (widen s22028_1 (by decide)))))))))))

theorem claim955 : CheckedClaim verifiedRow ⟨3,1,1,20040,24016,74560162022,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 20040 3977 ⟨74560216954,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim956 : CheckedClaim verifiedRow ⟨3,1,1,21002,21996,110883635251,158432054391⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 21002 995 ⟨110883690183,158431999459⟩
  rw [← get_eq_raw]
  exact (append (widen s21002_2 (by decide)) (append (widen s21004_4 (by decide)) (append (widen s21008_16 (by decide)) (append (widen s21024_32 (by decide)) (append (widen s21056_64 (by decide)) (append (widen s21120_128 (by decide)) (append (widen s21248_256 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide)))))))))))))))

theorem claim957 : CheckedClaim verifiedRow ⟨3,1,1,21034,22028,112257851948,160121307726⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 21034 995 ⟨112257906880,160121252794⟩
  rw [← get_eq_raw]
  exact (append (widen s21034_2 (by decide)) (append (widen s21036_4 (by decide)) (append (widen s21040_16 (by decide)) (append (widen s21056_64 (by decide)) (append (widen s21120_128 (by decide)) (append (widen s21248_256 (by decide)) (append (widen s21504_512 (by decide)) (append (widen s22016_8 (by decide)) (append (widen s22024_4 (by decide)) (widen s22028_1 (by decide)))))))))))

theorem claim958 : CheckedClaim verifiedRow ⟨3,1,1,21964,23952,156751875276,273230203096⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 21964 1989 ⟨156751930208,273230148164⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))

theorem claim959 : CheckedClaim verifiedRow ⟨3,1,1,22028,23022,160121197853,216524989997⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 22028 995 ⟨160121252785,216524935065⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_256 (by decide)) (append (widen s22784_128 (by decide)) (append (widen s22912_64 (by decide)) (append (widen s22976_32 (by decide)) (append (widen s23008_8 (by decide)) (append (widen s23016_4 (by decide)) (append (widen s23020_2 (by decide)) (widen s23022_1 (by decide)))))))))))))))

theorem claim960 : CheckedClaim verifiedRow ⟨3,1,1,22028,24016,160121197853,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 22028 1989 ⟨160121252785,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim961 : CheckedClaim verifiedRow ⟨3,1,1,23022,23519,216524880124,246689980531⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23022 498 ⟨216524935056,246689925599⟩
  rw [← get_eq_raw]
  exact (append (widen s23022_2 (by decide)) (append (widen s23024_16 (by decide)) (append (widen s23040_256 (by decide)) (append (widen s23296_128 (by decide)) (append (widen s23424_64 (by decide)) (widen s23488_32 (by decide)))))))

theorem claim962 : CheckedClaim verifiedRow ⟨3,1,1,23022,24016,216524880124,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23022 995 ⟨216524935056,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23022_2 (by decide)) (append (widen s23024_16 (by decide)) (append (widen s23040_512 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))

theorem claim963 : CheckedClaim verifiedRow ⟨3,1,1,23519,23767,246689870658,261904360446⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23519 249 ⟨246689925590,261904305514⟩
  rw [← get_eq_raw]
  exact (append (widen s23519_1 (by decide)) (append (widen s23520_32 (by decide)) (append (widen s23552_128 (by decide)) (append (widen s23680_64 (by decide)) (append (widen s23744_16 (by decide)) (widen s23760_8 (by decide)))))))

theorem claim964 : CheckedClaim verifiedRow ⟨3,1,1,23519,24016,246689870658,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23519 498 ⟨246689925590,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23519_1 (by decide)) (append (widen s23520_32 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide))))))))

theorem claim965 : CheckedClaim verifiedRow ⟨3,1,1,23767,23891,261904250573,269501804529⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23767 125 ⟨261904305505,269501749597⟩
  rw [← get_eq_raw]
  exact (append (widen s23767_1 (by decide)) (append (widen s23768_8 (by decide)) (append (widen s23776_32 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_16 (by decide)) (widen s23888_4 (by decide)))))))

theorem claim966 : CheckedClaim verifiedRow ⟨3,1,1,23767,24016,261904250573,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23767 250 ⟨261904305505,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23767_1 (by decide)) (append (widen s23768_8 (by decide)) (append (widen s23776_32 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide))))))))

theorem claim967 : CheckedClaim verifiedRow ⟨3,1,1,23891,23953,269501694656,273291258331⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23891 63 ⟨269501749588,273291203399⟩
  rw [← get_eq_raw]
  exact (append (widen s23891_1 (by decide)) (append (widen s23892_4 (by decide)) (append (widen s23896_8 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_2 (by decide)))))))

theorem claim968 : CheckedClaim verifiedRow ⟨3,1,1,23891,24016,269501694656,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23891 126 ⟨269501749588,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23891_1 (by decide)) (append (widen s23892_4 (by decide)) (append (widen s23896_8 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide))))))))

private theorem s24064_512 : Run get 24064 512 ⟨280051976813,310457109776⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨310514949710,338774449724⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨338826756532,363545713025⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨310514949710,363545713025⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

theorem claim969 : CheckedClaim verifiedRow ⟨3,1,1,23952,25940,273230093223,377358403721⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23952 1989 ⟨273230148155,377358348789⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide)))))))))))

private theorem s25600_512 : Run get 25600 512 ⟨363589675874,383314166338⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨383346931268,396642247214⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨363589675874,396642247214⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨310514949710,396642247214⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨396661082037,402200343068⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨398860114651,402291037194⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨396661082037,402291037194⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim970 : CheckedClaim verifiedRow ⟨3,1,1,23952,27928,273230093223,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23952 3977 ⟨273230148155,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim971 : CheckedClaim verifiedRow ⟨3,1,1,23953,23984,273291148458,275182781014⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23953 32 ⟨273291203390,275182726082⟩
  rw [← get_eq_raw]
  exact (append (widen s23953_1 (by decide)) (append (widen s23954_2 (by decide)) (append (widen s23956_4 (by decide)) (append (widen s23960_8 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))

theorem claim972 : CheckedClaim verifiedRow ⟨3,1,1,23953,24016,273291148458,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23953 64 ⟨273291203390,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23953_1 (by decide)) (append (widen s23954_2 (by decide)) (append (widen s23956_4 (by decide)) (append (widen s23960_8 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide))))))))

theorem claim973 : CheckedClaim verifiedRow ⟨3,1,1,23984,24016,275182671141,277132715652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23984 33 ⟨275182726073,277132660720⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide))))

theorem claim974 : CheckedClaim verifiedRow ⟨3,1,1,23984,27960,275182671141,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 23984 3977 ⟨275182726073,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim975 : CheckedClaim verifiedRow ⟨3,1,1,24016,24023,277132605779,277558883209⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 8 ⟨277132660711,277558828277⟩
  rw [← get_eq_raw]
  exact (widen s24016_8 (by decide))

theorem claim976 : CheckedClaim verifiedRow ⟨3,1,1,24016,24031,277132605779,278045756247⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 16 ⟨277132660711,278045701315⟩
  rw [← get_eq_raw]
  exact (widen s24016_16 (by decide))

theorem claim977 : CheckedClaim verifiedRow ⟨3,1,1,24016,24047,277132605779,279018922851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 32 ⟨277132660711,279018867919⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (widen s24032_16 (by decide)))

theorem claim978 : CheckedClaim verifiedRow ⟨3,1,1,24016,24078,277132605779,280902115751⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 63 ⟨277132660711,280902060819⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_8 (by decide)) (append (widen s24072_4 (by decide)) (append (widen s24076_2 (by decide)) (widen s24078_1 (by decide)))))))

theorem claim979 : CheckedClaim verifiedRow ⟨3,1,1,24016,24140,277132605779,284658391758⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 125 ⟨277132660711,284658336826⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_64 (by decide)) (append (widen s24128_8 (by decide)) (append (widen s24136_4 (by decide)) (widen s24140_1 (by decide)))))))

theorem claim980 : CheckedClaim verifiedRow ⟨3,1,1,24016,24264,277132605779,292122909063⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 249 ⟨277132660711,292122854131⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_128 (by decide)) (append (widen s24192_64 (by decide)) (append (widen s24256_8 (by decide)) (widen s24264_1 (by decide)))))))

theorem claim981 : CheckedClaim verifiedRow ⟨3,1,1,24016,24513,277132605779,306855557464⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 498 ⟨277132660711,306855502532⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_256 (by decide)) (append (widen s24320_128 (by decide)) (append (widen s24448_64 (by decide)) (widen s24512_2 (by decide)))))))

theorem claim982 : CheckedClaim verifiedRow ⟨3,1,1,24016,25010,277132605779,334707133622⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 995 ⟨277132660711,334707078690⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_256 (by decide)) (append (widen s24832_128 (by decide)) (append (widen s24960_32 (by decide)) (append (widen s24992_16 (by decide)) (append (widen s25008_2 (by decide)) (widen s25010_1 (by decide))))))))))

theorem claim983 : CheckedClaim verifiedRow ⟨3,1,1,24016,26004,277132605779,379668369457⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 1989 ⟨277132660711,379668314525⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_128 (by decide)) (append (widen s25984_16 (by decide)) (append (widen s26000_4 (by decide)) (widen s26004_1 (by decide))))))))))

theorem claim984 : CheckedClaim verifiedRow ⟨3,1,1,24016,27992,277132605779,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 3977 ⟨277132660711,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

private theorem s27648_512 : Run get 27648 512 ⟨385785247095,398844282038⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨362511856048,385749814810⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨362511856048,398844282038⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨362511856048,402291037194⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨310514949710,402291037194⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨329010864622,362456326852⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨285725571106,328935636307⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨285725571106,362456326852⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨233579325339,285631981931⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨173950596503,233469637559⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨173950596503,285631981931⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨173950596503,362456326852⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨108615526466,173827915342⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨39661028538,108483657631⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨39661028538,173827915342⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim985 : CheckedClaim verifiedRow ⟨3,1,1,24016,31968,8798009078,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24016 7953 ⟨8798064010,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim986 : CheckedClaim verifiedRow ⟨3,1,1,24023,24027,277558773336,277802343400⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24023 5 ⟨277558828268,277802288468⟩
  rw [← get_eq_raw]
  exact (append (widen s24023_1 (by decide)) (widen s24024_4 (by decide)))

theorem claim987 : CheckedClaim verifiedRow ⟨3,1,1,24023,24031,277558773336,278045756247⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24023 9 ⟨277558828268,278045701315⟩
  rw [← get_eq_raw]
  exact (append (widen s24023_1 (by decide)) (widen s24024_8 (by decide)))

theorem claim988 : CheckedClaim verifiedRow ⟨3,1,1,24027,24029,277802233527,277924055778⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24027 3 ⟨277802288459,277924000846⟩
  rw [← get_eq_raw]
  exact (append (widen s24027_1 (by decide)) (widen s24028_2 (by decide)))

theorem claim989 : CheckedClaim verifiedRow ⟨3,1,1,24027,24031,277802233527,278045756247⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24027 5 ⟨277802288459,278045701315⟩
  rw [← get_eq_raw]
  exact (append (widen s24027_1 (by decide)) (widen s24028_4 (by decide)))

theorem claim990 : CheckedClaim verifiedRow ⟨3,1,1,24029,24031,277923945905,278045756247⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24029 3 ⟨277924000837,278045701315⟩
  rw [← get_eq_raw]
  exact (append (widen s24029_1 (by decide)) (widen s24030_2 (by decide)))

theorem claim991 : CheckedClaim verifiedRow ⟨3,1,1,24031,24033,278045646374,278167444739⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24031 3 ⟨278045701306,278167389807⟩
  rw [← get_eq_raw]
  exact (append (widen s24031_1 (by decide)) (widen s24032_2 (by decide)))

theorem claim992 : CheckedClaim verifiedRow ⟨3,1,1,24031,24035,278045646374,278289121182⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24031 5 ⟨278045701306,278289066250⟩
  rw [← get_eq_raw]
  exact (append (widen s24031_1 (by decide)) (widen s24032_4 (by decide)))

theorem claim993 : CheckedClaim verifiedRow ⟨3,1,1,24031,24039,278045646374,278532437641⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24031 9 ⟨278045701306,278532382709⟩
  rw [← get_eq_raw]
  exact (append (widen s24031_1 (by decide)) (widen s24032_8 (by decide)))

theorem claim994 : CheckedClaim verifiedRow ⟨3,1,1,24031,24047,278045646374,279018922851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24031 17 ⟨278045701306,279018867919⟩
  rw [← get_eq_raw]
  exact (append (widen s24031_1 (by decide)) (widen s24032_16 (by decide)))

theorem claim995 : CheckedClaim verifiedRow ⟨3,1,1,24033,24035,278167334866,278289121182⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24033 3 ⟨278167389798,278289066250⟩
  rw [← get_eq_raw]
  exact (append (widen s24033_1 (by decide)) (widen s24034_2 (by decide)))

theorem claim996 : CheckedClaim verifiedRow ⟨3,1,1,24035,24039,278289011309,278532437641⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24035 5 ⟨278289066241,278532382709⟩
  rw [← get_eq_raw]
  exact (append (widen s24035_1 (by decide)) (widen s24036_4 (by decide)))

theorem claim997 : CheckedClaim verifiedRow ⟨3,1,1,24039,24047,278532327768,279018922851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24039 9 ⟨278532382700,279018867919⟩
  rw [← get_eq_raw]
  exact (append (widen s24039_1 (by decide)) (widen s24040_8 (by decide)))

theorem claim998 : CheckedClaim verifiedRow ⟨3,1,1,24047,24078,279018812978,280902115751⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24047 32 ⟨279018867910,280902060819⟩
  rw [← get_eq_raw]
  exact (append (widen s24047_1 (by decide)) (append (widen s24048_16 (by decide)) (append (widen s24064_8 (by decide)) (append (widen s24072_4 (by decide)) (append (widen s24076_2 (by decide)) (widen s24078_1 (by decide)))))))

theorem claim999 : CheckedClaim verifiedRow ⟨3,1,1,24078,24140,280902005878,284658391758⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24078 63 ⟨280902060810,284658336826⟩
  rw [← get_eq_raw]
  exact (append (widen s24078_2 (by decide)) (append (widen s24080_16 (by decide)) (append (widen s24096_32 (by decide)) (append (widen s24128_8 (by decide)) (append (widen s24136_4 (by decide)) (widen s24140_1 (by decide)))))))

theorem claim1000 : CheckedClaim verifiedRow ⟨3,1,1,24140,24264,284658281885,292122909063⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24140 125 ⟨284658336817,292122854131⟩
  rw [← get_eq_raw]
  exact (append (widen s24140_4 (by decide)) (append (widen s24144_16 (by decide)) (append (widen s24160_32 (by decide)) (append (widen s24192_64 (by decide)) (append (widen s24256_8 (by decide)) (widen s24264_1 (by decide)))))))

theorem claim1001 : CheckedClaim verifiedRow ⟨3,1,1,24264,24513,292122799190,306855557464⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24264 250 ⟨292122854122,306855502532⟩
  rw [← get_eq_raw]
  exact (append (widen s24264_8 (by decide)) (append (widen s24272_16 (by decide)) (append (widen s24288_32 (by decide)) (append (widen s24320_128 (by decide)) (append (widen s24448_64 (by decide)) (widen s24512_2 (by decide)))))))

theorem claim1002 : CheckedClaim verifiedRow ⟨3,1,1,24513,25010,306855447591,334707133622⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 24513 498 ⟨306855502523,334707078690⟩
  rw [← get_eq_raw]
  exact (append (widen s24513_1 (by decide)) (append (widen s24514_2 (by decide)) (append (widen s24516_4 (by decide)) (append (widen s24520_8 (by decide)) (append (widen s24528_16 (by decide)) (append (widen s24544_32 (by decide)) (append (widen s24576_256 (by decide)) (append (widen s24832_128 (by decide)) (append (widen s24960_32 (by decide)) (append (widen s24992_16 (by decide)) (append (widen s25008_2 (by decide)) (widen s25010_1 (by decide)))))))))))))

theorem claim1003 : CheckedClaim verifiedRow ⟨3,1,1,25010,26004,334707023749,379668369457⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 25010 995 ⟨334707078681,379668314525⟩
  rw [← get_eq_raw]
  exact (append (widen s25010_2 (by decide)) (append (widen s25012_4 (by decide)) (append (widen s25016_8 (by decide)) (append (widen s25024_64 (by decide)) (append (widen s25088_512 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_128 (by decide)) (append (widen s25984_16 (by decide)) (append (widen s26000_4 (by decide)) (widen s26004_1 (by decide)))))))))))

theorem claim1004 : CheckedClaim verifiedRow ⟨3,1,1,25940,27928,377358293848,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 25940 1989 ⟨377358348780,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim1005 : CheckedClaim verifiedRow ⟨3,1,1,25972,27960,378525119962,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 25972 1989 ⟨378525174894,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s25972_4 (by decide)) (append (widen s25976_8 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim1006 : CheckedClaim verifiedRow ⟨3,1,1,26004,27992,379668259584,402291092126⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 26004 1989 ⟨379668314516,402291037194⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

theorem claim1007 : CheckedClaim verifiedRow ⟨3,1,1,27992,29980,257713930839,391156497394⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 27992 1989 ⟨257713985771,391156442462⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_256 (by decide)) (append (widen s29952_16 (by decide)) (append (widen s29968_8 (by decide)) (append (widen s29976_4 (by decide)) (widen s29980_1 (by decide)))))))))))

theorem claim1008 : CheckedClaim verifiedRow ⟨3,1,1,27992,31968,8798009078,391156497394⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 27992 3977 ⟨8798064010,391156442462⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim1009 : CheckedClaim verifiedRow ⟨3,1,1,29948,31936,13195589611,260989856643⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 29948 1989 ⟨13195644543,260989801711⟩
  rw [← get_eq_raw]
  exact (append (widen s29948_4 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))

theorem claim1010 : CheckedClaim verifiedRow ⟨3,1,1,29980,31968,8798009078,257714040712⟩ := by
  change Run (rawBlock verifiedRow 3 1 .first) 29980 1989 ⟨8798064010,257713985780⟩
  rw [← get_eq_raw]
  exact (append (widen s29980_4 (by decide)) (append (widen s29984_32 (by decide)) (append (widen s30016_64 (by decide)) (append (widen s30080_128 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
