import CertTreeRanges
import CertTreeInterpolation

/-! A closed mesh range from the first to the last node, widened by the
piecewise-linear interpolation error. -/
namespace GaussianChains.Cert.Tables
open Set

/-- Round the interpolation error up to the output lattice used by the table. -/
def interpolationPad (M unit : ℕ+) (cap : ℚ) : ℚ :=
  (⌈cap / (8*(M:ℚ)^2) * (unit:ℚ)⌉ : ℚ) / unit

theorem interpolationPad_ge (M unit : ℕ+) (cap : ℚ) :
    (cap:ℝ) / (8*(M:ℝ)^2) ≤ (interpolationPad M unit cap : ℝ) := by
  have h : cap / (8*(M:ℚ)^2) ≤ interpolationPad M unit cap :=
    (le_div_iff₀ (show 0 < (unit:ℚ) by exact_mod_cast unit.2)).mpr (Int.le_ceil _)
  exact_mod_cast h

theorem meshHull_mem {f f' f'' : ℝ → ℝ} {cap : ℝ} {e : ℚ} (M : ℕ+)
    {a b : ℕ} {node : ℕ → Interval} (hab : a ≤ b) (hb : b ≤ (M:ℕ))
    (h₁ : ∀ y, HasDerivAt f (f' y) y) (h₂ : ∀ y, HasDerivAt f' (f'' y) y)
    (hcap : ∀ y, |f'' y| ≤ cap) (hpad : cap/(8*(M:ℝ)^2) ≤ (e:ℝ))
    (hn : ∀ p ≤ (M:ℕ), (node p).Mem (f ((p:ℝ)/M))) {x : ℝ}
    (hx : x ∈ Icc ((a:ℝ)/M) ((b:ℝ)/M)) :
    (pad (rangeHull node a b) e).Mem (f x) := by
  have hm : (0:ℝ) < M := by exact_mod_cast M.2
  have hc : 0 ≤ cap := (abs_nonneg _).trans (hcap x)
  have he : (0:ℝ) ≤ e := (div_nonneg hc (by positivity)).trans hpad
  by_cases hxend : x = (b:ℝ)/M
  · subst x
    apply pad_mem (rangeHull_mem hab le_rfl (hn b hb))
    simpa using he
  let p := ⌊x*(M:ℝ)⌋₊
  have ha : (a:ℝ) ≤ x*M := (div_le_iff₀ hm).mp hx.1
  have hxb : x*(M:ℝ) < b := (lt_div_iff₀ hm).mp (lt_of_le_of_ne hx.2 hxend)
  have hpos : 0 ≤ x*(M:ℝ) := (Nat.cast_nonneg _).trans ha
  have hap : a ≤ p := (Nat.le_floor_iff hpos).mpr ha
  have hpb : p < b := (Nat.floor_lt hpos).mpr hxb
  have hnext := Nat.succ_le_of_lt hpb
  have hcell : x ∈ Icc ((p:ℝ)/M) (((p+1:ℕ):ℝ)/M) := by
    refine ⟨(div_le_iff₀ hm).mpr (Nat.floor_le hpos), (le_div_iff₀ hm).mpr ?_⟩
    simpa [p] using (Nat.lt_floor_add_one (x*(M:ℝ))).le
  have hlt : (p:ℝ)/M < ((p+1:ℕ):ℝ)/M := by gcongr; omega
  let I := rangeHull node a b
  have hl : I.Mem (f ((p:ℝ)/M)) := rangeHull_mem hap hpb.le (hn p (hpb.le.trans hb))
  have hr : I.Mem (f (((p+1:ℕ):ℝ)/M)) := rangeHull_mem (by omega) hnext
    (hn _ (hnext.trans hb))
  have hout := Certificate.interpolation_enclosure hlt hcell hc (fun y _ => h₁ y)
    (fun y _ => h₂ y) (fun y _ => hcap y) hl hr
  have hstep : cap * (((p+1:ℕ):ℝ)/M-(p:ℝ)/M)^2 / 8 = cap / (8*(M:ℝ)^2) := by
    push_cast
    field_simp
    ring
  rw [hstep] at hout
  change ((I.lo-e:ℚ):ℝ) ≤ f x ∧ f x ≤ ((I.hi+e:ℚ):ℝ)
  push_cast
  exact ⟨by linarith [hout.1], by linarith [hout.2]⟩

end GaussianChains.Cert.Tables
