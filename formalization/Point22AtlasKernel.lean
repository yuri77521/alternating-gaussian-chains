import CertTreeGrid
import CertTreeAtlasCaps
import CertTreeRanges
import CertTreeMeshHull
import Mathlib.Tactic.FieldSimp

/-! Signed block kernels for the independent 32000-node width-22 atlas.
Adjacent sites in a packed block have separation 32 grid units. -/

namespace GaussianChains.Point22.Atlas

open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds
open GaussianChains.ImageCalculus

def orderCap : Order → ℚ
  | .value => 44 | .first => 1500 | .second => 22000

noncomputable def mode (n : ℕ) : ℝ → ℝ := deriv^[n] (kernel 22)

theorem mode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (mode n) (mode (n+1) x) x := by
  simp only [mode, kernel_iterated_deriv (by norm_num : 0 < (22:ℝ)),
    Function.iterate_succ_apply']
  exact periodized_derivative (by norm_num) _ _

theorem mode_add_int (n : ℕ) (x : ℝ) (t : ℤ) : mode n (x+t) = mode n x := by
  rw [mode, kernel_iterated_deriv (by norm_num : 0 < (22:ℝ))]
  unfold periodized
  conv_rhs => rw [← (Equiv.addRight t).tsum_eq]
  apply tsum_congr
  intro k
  simp [imageTerm, Equiv.coe_addRight, add_assoc, add_comm, add_left_comm]

def blockSign (i j : ℕ) : ℚ := (-1:ℚ)^(i+j)
def shift (i j : ℕ) : ℚ := ((j:ℚ)-i)/1000

noncomputable def blockValue (leftSize rightSize n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range leftSize, ∑ j ∈ Finset.range rightSize,
    (blockSign i j:ℝ) * mode n (x + (shift i j:ℝ))

theorem blockValue_hasDerivAt (a b n : ℕ) (x : ℝ) :
    HasDerivAt (blockValue a b n) (blockValue a b (n+1) x) x := by
  unfold blockValue
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  simpa [Function.comp_def] using
    (((mode_hasDerivAt n (x+(shift i j:ℝ))).comp x ((hasDerivAt_id x).add_const _)).const_mul
      (blockSign i j:ℝ))

theorem blockValue_cap (a b : ℕ) (j : Order) (x : ℝ) :
    |blockValue a b (orderIndex j+2) x| ≤ (a:ℝ)*b*(orderCap j:ℝ) := by
  have ht (y : ℝ) : |mode (orderIndex j+2) y| ≤ (orderCap j:ℝ) := by
    obtain ⟨h₂,h₃,h₄⟩ := FourierBounds.point_atlas_caps y
    cases j <;> first | exact h₂ | exact h₃ | exact h₄
  have hterm (i l : ℕ) :
      |(blockSign i l:ℝ)*mode (orderIndex j+2) (x+(shift i l:ℝ))| ≤ (orderCap j:ℝ) := by
    simpa [blockSign, abs_mul, abs_pow] using ht (x+(shift i l:ℝ))
  unfold blockValue
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range a, ∑ _l ∈ Finset.range b, (orderCap j:ℝ) := by
      apply Finset.sum_le_sum; intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hterm i l)
    _ = _ := by simp; ring

def meshIndex (p i j : ℕ) : ℤ := (p:ℤ)+((j:ℤ)-i)*32
def residue (p i j : ℕ) : ℕ := (meshIndex p i j % 32000).toNat

theorem residue_lt (p i j : ℕ) : residue p i j < 32000 := by
  unfold residue
  have h := Int.emod_lt_of_pos (meshIndex p i j) (by decide : (0:ℤ)<32000)
  omega

theorem mode_residue (n p i j : ℕ) :
    mode n ((p:ℝ)/32000 + (shift i j:ℝ)) = mode n ((residue p i j:ℝ)/32000) := by
  let k := meshIndex p i j / 32000
  have hr : ((residue p i j:ℕ):ℤ) = meshIndex p i j % 32000 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have h : ((residue p i j : ℕ):ℤ) + 32000*k = meshIndex p i j := by
    rw [hr]
    exact Int.emod_add_mul_ediv _ _
  have he := congrArg (fun t : ℤ => (t : ℝ)) h
  simp [meshIndex] at he
  rw [show (p:ℝ)/32000 + (shift i j:ℝ) = (residue p i j:ℝ)/32000 + k by
    push_cast [shift]; linarith, mode_add_int]

private def sumI (n : ℕ) (f : ℕ → Interval) : Interval :=
  ⟨∑ i ∈ Finset.range n, (f i).lo, ∑ i ∈ Finset.range n, (f i).hi⟩

private theorem sumI_mem {n : ℕ} {f : ℕ → Interval} {g : ℕ → ℝ}
    (h : ∀ i ∈ Finset.range n, (f i).Mem (g i)) : (sumI n f).Mem (∑ i ∈ Finset.range n, g i) := by
  constructor
  · simpa [sumI] using Finset.sum_le_sum (fun i hi => (h i hi).1)
  · simpa [sumI] using Finset.sum_le_sum (fun i hi => (h i hi).2)

/-- For equal shifts i-j the summands have identical signs. This is the
ungrouped form of the signed multiplicities in the atlas generator. -/
def blockNodeFrom (node : Order → ℕ → Interval) (a b : ℕ) (ord : Order) (p : ℕ) : Interval :=
  sumI a fun i => sumI b fun j =>
    (Interval.singleton (blockSign i j)).mul (node ord (residue p i j))

theorem blockNodeFrom_sound {node : Order → ℕ → Interval}
    (hn : ∀ ord p, p < 32000 → (node ord p).Mem (mode (orderIndex ord) ((p:ℝ)/32000)))
    (a b : ℕ) (ord : Order) (p : ℕ) :
    (blockNodeFrom node a b ord p).Mem (blockValue a b (orderIndex ord) ((p:ℝ)/32000)) := by
  apply sumI_mem; intro i _
  apply sumI_mem; intro j _
  rw [mode_residue]
  exact Interval.mul_mem (Interval.singleton_mem _) (hn ord _ (residue_lt p i j))

def atlasNode : Order → ℕ → Interval := gridNode (10^35) (10^11) 32000 22

theorem atlasNode_sound (ord : Order) (p : ℕ) (hp : p < 32000) :
    (atlasNode ord p).Mem (mode (orderIndex ord) ((p:ℝ)/32000)) :=
  gridNode_point_sound _ _ _ (by decide) _ hp.le

/-- The error pad is rounded away from zero on the atlas output grid. -/
def blockPad (a b : ℕ) (ord : Order) : ℚ :=
  (⌈(a:ℚ)*b*orderCap ord*10^11/(8*32000^2)⌉ : ℚ)/10^11

def atlasBlockRangeFrom (node : Order → ℕ → Interval) (a b : ℕ) (ord : Order)
    (first last : ℕ) : Interval :=
  Tables.pad (rangeHull (blockNodeFrom node a b ord) first last) (blockPad a b ord)

def atlasBlockRange := atlasBlockRangeFrom atlasNode

theorem atlasBlockRangeFrom_sound {node : Order → ℕ → Interval}
    (hn : ∀ j p, p < 32000 → (node j p).Mem (mode (orderIndex j) ((p:ℝ)/32000)))
    (a b : ℕ) (ord : Order) {first last : ℕ} (hab : first ≤ last) (hb : last ≤ 32000)
    {x : ℝ} (hx : x ∈ Set.Icc ((first:ℝ)/32000) ((last:ℝ)/32000)) :
    (atlasBlockRangeFrom node a b ord first last).Mem (blockValue a b (orderIndex ord) x) := by
  have hq : (a:ℚ)*b*orderCap ord/(8*32000^2) ≤ blockPad a b ord := by
    unfold blockPad
    apply (le_div_iff₀ (by norm_num)).mpr
    convert Int.le_ceil ((a:ℚ)*b*orderCap ord*10^11/(8*32000^2)) using 1
    ring
  apply meshHull_mem (M := 32000) hab hb (blockValue_hasDerivAt a b _)
    (blockValue_hasDerivAt a b _) (blockValue_cap a b ord)
  · exact_mod_cast hq
  · intro p _
    exact blockNodeFrom_sound hn a b ord p
  · exact hx

theorem atlasBlockRange_sound (a b : ℕ) (ord : Order) {first last : ℕ}
    (hab : first ≤ last) (hb : last ≤ 32000)
    {x : ℝ} (hx : x ∈ Set.Icc ((first:ℝ)/32000) ((last:ℝ)/32000)) :
    (atlasBlockRange a b ord first last).Mem (blockValue a b (orderIndex ord) x) :=
  atlasBlockRangeFrom_sound atlasNode_sound a b ord hab hb hx

end GaussianChains.Point22.Atlas
