import Point22AtlasKernel
import Point22Contacts
import CertTreeVariations

/-! Assembly of the signed inter-block score and of its first and second
derivatives in the normalized physical start coordinates. -/
namespace GaussianChains.Point22.Atlas

open GaussianChains.Cert GaussianChains.ImageBounds

def active (w : Word) (i j : Fin 6) : Prop := i < j ∧ j.val < w.blocks.length
instance (w : Word) (i j : Fin 6) : Decidable (active w i j) := by unfold active; infer_instance

def blockSize (w : Word) (i : Fin 6) := w.blocks[i.val]?.getD 0
def firstSite (w : Word) (i : Fin 6) := (w.blocks.take i.val).sum
def pairSign (w : Word) (i j : Fin 6) : ℚ := (-1)^(firstSite w j - firstSite w i)

def blockTranslation (y v : Fin 6 → ℝ) (t : ℝ) : Fin 6 → ℝ := fun i => y i + v i*t

@[simp] theorem blockTranslation_zero (y v : Fin 6 → ℝ) : blockTranslation y v 0 = y := by
  funext i
  simp [blockTranslation]

/-- For two sites in the same block, the common starting charge cancels. -/
noncomputable def internalScore (w : Word) : ℝ :=
  ∑ a : Fin 6, ∑ i ∈ Finset.range (blockSize w a), ∑ j ∈ Finset.range (blockSize w a),
    if i < j then (blockSign i j : ℝ) * mode 0 (shift i j) else 0

/-- The value (order zero) and directional derivatives in an arbitrary
physical displacement direction. -/
noncomputable def directional (w : Word) (y v : Fin 6 → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, if active w i j then
    (pairSign w i j : ℝ) * (v j - v i)^n * blockValue (blockSize w i) (blockSize w j) n (y j-y i)
  else 0

noncomputable def atlasScore (w : Word) (y : Fin 6 → ℝ) (internal : ℝ) : ℝ :=
  internal + directional w y 0 0

def basisDir (k : ℕ) (i : Fin 6) : ℚ := if i.val = k then 1 else 0
def encodedDir (code : ℕ) (i : Fin 6) : ℚ := ((code / 3^i.val % 3 : ℕ) : ℚ) - 1

noncomputable def realQuantity (w : Word) (y : Fin 6 → ℝ) (internal witness : ℝ) :
    Quantity → ℝ
  | .feasible _ => 0
  | .score _ => atlasScore w y internal - witness
  | .gradient k => directional w y (fun i => (basisDir k i : ℝ)) 1
  | .curvature k => directional w y (fun i => (encodedDir k i : ℝ)) 2

private def sumIntervals (f : Fin 6 → Interval) : Interval :=
  ⟨∑ i, (f i).lo, ∑ i, (f i).hi⟩

private theorem sumIntervals_mem {f : Fin 6 → Interval} {g : Fin 6 → ℝ}
    (h : ∀ i, (f i).Mem (g i)) : (sumIntervals f).Mem (∑ i, g i) := by
  constructor
  · simpa [sumIntervals] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).1)
  · simpa [sumIntervals] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).2)

private def orderedInterval (w : Word) (pairI : Fin 6 → Fin 6 → Order → Interval)
    (v : Fin 6 → ℚ) (ord : Order) : Interval :=
  sumIntervals fun i => sumIntervals fun j =>
    let c := pairSign w i j * (v j-v i)^orderIndex ord
    if active w i j ∧ c ≠ 0 then (Interval.singleton c).mul (pairI i j ord)
    else Interval.singleton 0

/-- The oracle passes intervals for *unsigned* block kernels. The prefactor
uses the parity of the two block starts, while the individual sites' signs
have already been incorporated in each kernel. -/
def quantities (w : Word) (pairI : Fin 6 → Fin 6 → Order → Interval)
    (internal witness : Interval) : Quantity → Interval
  | .feasible _ => .singleton 0
  | .score _ => (internal.add (orderedInterval w pairI 0 .value)).add witness.neg
  | .gradient k => orderedInterval w pairI (basisDir k) .first
  | .curvature k => orderedInterval w pairI (encodedDir k) .second

private theorem orderedInterval_mem (w : Word) (y : Fin 6 → ℝ)
    (pairI : Fin 6 → Fin 6 → Order → Interval) (v : Fin 6 → ℚ) (ord : Order)
    (hp : ∀ i j, active w i j → ∀ o, (pairI i j o).Mem
      (blockValue (blockSize w i) (blockSize w j) (orderIndex o) (y j-y i))) :
    (orderedInterval w pairI v ord).Mem (directional w y (fun i => (v i : ℝ)) (orderIndex ord)) := by
  unfold orderedInterval directional
  apply sumIntervals_mem
  intro i
  apply sumIntervals_mem
  intro j
  dsimp only
  by_cases hij : active w i j
  · rw [if_pos hij]
    by_cases hc : pairSign w i j * (v j-v i)^orderIndex ord = 0
    · rw [if_neg (by simp [hc])]
      have hzero := congrArg (fun u : ℚ => (u:ℝ)) hc
      push_cast at hzero
      simp [hzero,Interval.singleton,Interval.Mem]
    · rw [if_pos ⟨hij,hc⟩]
      simpa only [Rat.cast_mul,Rat.cast_sub,Rat.cast_pow] using
        Interval.mul_mem (Interval.singleton_mem (pairSign w i j * (v j-v i)^orderIndex ord))
          (hp i j hij ord)
  · simp [hij,Interval.singleton,Interval.Mem]

theorem quantities_sound (w : Word) (y : Fin 6 → ℝ)
    {pairI : Fin 6 → Fin 6 → Order → Interval} {A B : Interval} {a b : ℝ}
    (ha : A.Mem a) (hb : B.Mem b)
    (hp : ∀ i j, active w i j → ∀ o, (pairI i j o).Mem
      (blockValue (blockSize w i) (blockSize w j) (orderIndex o) (y j-y i))) (k : Quantity) :
    (quantities w pairI A B k).Mem (realQuantity w y a b k) := by
  cases k with
  | feasible _ => simp [quantities,realQuantity,Interval.singleton,Interval.Mem]
  | score _ =>
    simpa [quantities,realQuantity,atlasScore,orderIndex,sub_eq_add_neg] using
      Interval.add_mem (Interval.add_mem ha (orderedInterval_mem w y pairI 0 .value hp)) (Interval.neg_mem hb)
  | gradient k => exact orderedInterval_mem w y pairI (basisDir k) .first hp
  | curvature k => exact orderedInterval_mem w y pairI (encodedDir k) .second hp

theorem directional_hasDerivAt (w : Word) (y v : Fin 6 → ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u => directional w (blockTranslation y v u) v n)
      (directional w (blockTranslation y v t) v (n+1)) t := by
  unfold directional
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  by_cases h : active w i j
  · simp only [h, if_true]
    have ha (i : Fin 6) : HasDerivAt (fun u => blockTranslation y v u i) (v i) t := by
      simpa [blockTranslation] using (((hasDerivAt_id t).const_mul (v i)).const_add (y i))
    have H := ((blockValue_hasDerivAt (blockSize w i) (blockSize w j) n _).comp t
      ((ha j).sub (ha i))).const_mul ((pairSign w i j : ℝ) * (v j-v i)^n)
    convert H using 1 <;> simp only [Pi.sub_apply, pow_succ] <;> ring
  · simpa only [h, if_false] using hasDerivAt_const t (0:ℝ)

theorem atlasScore_hasDerivAt (w : Word) (y v : Fin 6 → ℝ) (internal t : ℝ) :
    HasDerivAt (fun u => atlasScore w (blockTranslation y v u) internal)
      (directional w (blockTranslation y v t) v 1) t := by
  simpa [atlasScore,directional] using (directional_hasDerivAt w y v 0 t).const_add internal

theorem realQuantity_necessary (w : Word) (y : Fin 6 → ℝ) (internal witness : ℝ)
    (hscore : witness ≤ atlasScore w y internal)
    (hmax : ∀ v : Fin 6 → ℝ, IsLocalMax (fun t => atlasScore w (blockTranslation y v t) internal) 0)
    (k : Quantity) : Necessary k (realQuantity w y internal witness k) := by
  cases k with
  | feasible _ => exact le_rfl
  | score _ => exact sub_nonneg.mpr hscore
  | gradient k =>
    let v : Fin 6 → ℝ := fun i => basisDir k i
    have he := (atlasScore_hasDerivAt w y v internal 0).deriv
    rw [(hmax v).deriv_eq_zero] at he
    simpa [Necessary,realQuantity,v] using he.symm
  | curvature k =>
    let v : Fin 6 → ℝ := fun i => encodedDir k i
    have hd : deriv (fun t => atlasScore w (blockTranslation y v t) internal) =
        fun t => directional w (blockTranslation y v t) v 1 :=
      funext fun t => (atlasScore_hasDerivAt w y v internal t).deriv
    have h := (necessary_transfer (hmax v) (atlasScore_hasDerivAt w y v internal 0).continuousAt).2
    rw [hd,(directional_hasDerivAt w y v 1 0).deriv] at h
    simpa [Necessary,realQuantity,v] using h

end GaussianChains.Point22.Atlas
