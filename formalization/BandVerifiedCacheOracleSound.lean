import BandVerifiedCacheOracle
import BandGlobal

/-! Soundness of a single accepted packet checked using a materialized raw
oracle. No equality with a particular implementation of the table is needed. -/
namespace GaussianChains.Band.Fast

open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds
open GaussianChains.FourierBounds GaussianChains.Strip

private theorem ref_in_strip (s : Slab) : (s.anchor:ℝ) ∈ Set.Icc (8:ℝ) 9 := by
  have hs := anchor_range s
  exact ⟨by exact_mod_cast hs.1,by exact_mod_cast hs.2⟩

theorem Valid.query_mem {s : Slab} {C : RawOracle} (V : Valid s C) (j : Order)
    {l r : ℚ} (hl : 0 ≤ l) (hr : r ≤ 1) {x : ℝ} (hx : (l:ℝ) ≤ x ∧ x ≤ (r:ℝ)) :
    (C.query j l r).Mem ((deriv^[orderIndex j] (kernel (s.anchor:ℝ))) x) := by
  have hs := ref_in_strip s
  have hs0 : (0:ℝ) < s.anchor := by linarith [hs.1]
  have hl' : (0:ℝ) ≤ l := by exact_mod_cast hl
  have hr' : (r:ℝ) ≤ 1 := by exact_mod_cast hr
  have hL : nearest 8192 l ≤ nearestReal 8192 x := by
    rw [← nearest_cast]; exact nearestReal_mono 8192 hx.1
  have hR : nearestReal 8192 x ≤ nearest 8192 r := by
    rw [← nearest_cast]; exact nearestReal_mono 8192 hx.2
  have hlast : nearest 8192 r ≤ 8192 := by
    rw [← nearest_cast]
    exact (nearest_bound (M:=8192) ((hl'.trans hx.1).trans hx.2) hr').1
  obtain ⟨ha,hb⟩ := V.range_cover j hL hR hlast
  have hcap (t : ℝ) : |deriv (deriv^[orderIndex j] (kernel (s.anchor:ℝ))) t| ≤ (stripCap j:ℝ) := by
    obtain ⟨h₁,h₂,h₃⟩ := strip_derivative_caps hs t
    cases j with
    | value => simpa [orderIndex,stripCap] using h₁.le
    | first => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₂.le
    | second => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₃.le
  have hnear := paddedNode_mem (cap:=stripCap j) (by cases j <;> norm_num [stripCap])
    (kernel_differentiable_order hs0 _) hcap 8192 1000000000 (V.raw_mem j)
    (hl'.trans hx.1) (hx.2.trans hr')
  exact ⟨(Rat.cast_le.mpr ha).trans hnear.1,hnear.2.trans (Rat.cast_le.mpr hb)⟩

theorem Valid.oracle_mem {s : Slab} {C : RawOracle} (V : Valid s C) {width : ℝ}
    (hw : s.width.Mem width) (r : Terminal) (I : Interval) (x : ℝ)
    (hx : I.Mem x) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (oracle s C (order r) I).Mem (s.field width (order r) x) := by
  have ho : orderIndex (imageOrder (order r)) = order r := by cases r <;> rfl
  have hlt : order r < 3 := by cases r <;> norm_num [order]
  apply pad_mem (y := deriv^[order r] (kernel (s.anchor:ℝ)) x)
  · have hr := V.query_mem (imageOrder (order r))
      (le_max_left 0 I.lo) (min_le_left 1 I.hi)
      (show ((max 0 I.lo:ℚ):ℝ) ≤ x ∧ x ≤ ((min 1 I.hi:ℚ):ℝ) by
        simpa using And.intro (max_le h0 hx.1) (le_min h1 hx.2))
    rwa [ho] at hr
  · exact width_perturbation s hw ⟨_,hlt⟩ x

theorem Valid.taylor_error {s : Slab} {C : RawOracle} (V : Valid s C) {q : ℚ}
    (hq : q ∈ Set.Icc (0:ℚ) 1) (checked : C.accurate q = true) :
    |kernel (s.anchor:ℝ) (q:ℝ) - (C.taylor q:ℝ)| ≤ (taylorBudget 8192 1000000000 20:ℝ) := by
  have hs := ref_in_strip s
  have hs0 : (0:ℝ) < s.anchor := by linarith [hs.1]
  have hp : nearest 8192 q ≤ 8192 := by
    rw [← nearest_cast]
    exact (nearest_bound (M:=8192) (by exact_mod_cast hq.1) (by exact_mod_cast hq.2)).1
  have hd (n : ℕ) (x : ℝ) := (kernel_differentiable_order hs0 n x).hasDerivAt
  simp only [RawOracle.accurate,Bool.and_eq_true] at checked
  exact taylorAt_sound (K:=20) (f:=kernel (s.anchor:ℝ)) (f':=deriv (kernel (s.anchor:ℝ)))
    (f'':=deriv^[2] (kernel (s.anchor:ℝ))) (by norm_num) (hd 0) (hd 1)
    (fun t => (strip_derivative_caps hs t).2.1.le) 8192 1000000000 hq
    (V.raw_mem .value _ hp) (V.raw_mem .first _ hp) checked.1 checked.2

theorem realTest_sound (s : Slab) (C : RawOracle) (V : Valid s C) {width h : ℝ}
    (hw : s.width.Mem width)
    (hF : ∀ x, HasDerivAt (s.field width 0) (s.field width 1 x) x)
    {floor : Interval} {B : Box 6} {u : Fin 6 → ℝ} (A : Support) (j : Fin 5)
    (hh : floor.Mem h) (h0 : 0 ≤ h) (h6 : h ≤ 1/6) (hm : B.Mem u) (hs : simplex u)
    (w : Witness) (pass : realTest s C floor A j B w = true) :
    ¬Stationary A j (s.field width) h u := by
  cases w with
  | transfer r => exact testLeaf_sound (V.oracle_mem hw) hh h0 h6 hm hs r pass
  | centered c =>
    apply valueTest_sound hF (V.oracle_mem hw (.gradient 0)) _ hh hm hs pass
    intro d hd ok
    have h₁ := width_perturbation s hw (0 : Fin 3) (d:ℝ)
    have h₂ := V.taylor_error hd ok
    have htriangle := abs_sub_le (s.field width 0 (d:ℝ)) (kernel (s.anchor:ℝ) (d:ℝ)) (C.taylor d:ℝ)
    change |s.field width 0 (d:ℝ)-(C.taylor d:ℝ)| ≤
      ((taylorBudget 8192 1000000000 20+s.radius 0:ℚ):ℝ)
    push_cast
    change |s.field width 0 (d:ℝ)-kernel (s.anchor:ℝ) (d:ℝ)| ≤ (s.radius 0:ℝ) at h₁
    linarith only [htriangle,h₁,h₂]

/-- Passing the indexed packet rules out global minimizers with its specified
support, for every allowed real width, gap floor and maximal-gap tie. -/
theorem checkRow_sound (s : Slab) (C : RawOracle) (V : Valid s C)
    (b : Fin s.count) (i : Fin 18) (pass : checkRow s C b i = true) : RowExcluded s b i := by
  apply rowExcluded_of_packet s b i pass
  intro width h hwidth hw hh h0 h6 j B w u checked hm hs _ _
  apply realTest_sound s C V hw _ _ j hh h0 h6.le hm hs w checked
  exact WidthBounds.matched_hasDerivAt (a:=(s.anchor:ℝ)) hwidth 0

#print axioms checkRow_sound

end GaussianChains.Band.Fast
