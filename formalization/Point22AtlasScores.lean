import Point22AtlasQuantities
import CertRootCoordinates
import ChainScore

/-! Scores independent of the branch-and-bound box. Packed within-block
pairs and the trial cell X are evaluated at exact width-22 mesh nodes. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds Finset

private def isum {ι : Type*} (s : Finset ι) (f : ι → Interval) : Interval :=
  ⟨∑ i ∈ s, (f i).lo, ∑ i ∈ s, (f i).hi⟩

private theorem isum_mem {ι : Type*} {s : Finset ι} {f : ι → Interval} {g : ι → ℝ}
    (h : ∀ i ∈ s, (f i).Mem (g i)) : (isum s f).Mem (∑ i ∈ s, g i) := by
  constructor
  · simpa [isum] using sum_le_sum (fun i hi => (h i hi).1)
  · simpa [isum] using sum_le_sum (fun i hi => (h i hi).2)

def internalFrom (node : Order → ℕ → Interval) (w : Word) : Interval :=
  isum univ fun a : Fin 6 => isum (range (blockSize w a)) fun i =>
    isum (range (blockSize w a)) fun j =>
      if i < j then (Interval.singleton (blockSign i j)).mul (node .value ((j-i)*32))
      else .singleton 0

private theorem blockSize_bound (w : Word) : ∀ a, blockSize w a ≤ 6 := by
  cases w <;> decide

theorem internalFrom_sound {node : Order → ℕ → Interval}
    (hn : ∀ o p, p < 32000 → (node o p).Mem (mode (orderIndex o) ((p:ℝ)/32000))) (w : Word) :
    (internalFrom node w).Mem (internalScore w) := by
  apply isum_mem; intro a _
  apply isum_mem; intro i _
  apply isum_mem; intro j hj
  by_cases hij : i < j
  · simp only [hij, if_true]
    apply Interval.mul_mem (Interval.singleton_mem _)
    have hp : (j-i)*32 < 32000 := by
      have := mem_range.mp hj
      have := blockSize_bound w a
      omega
    have h := hn .value _ hp
    have he : ((j-i)*32 : ℕ)/ (32000:ℝ) = (shift i j : ℝ) := by
      push_cast [Nat.cast_sub hij.le, shift]
      ring
    rw [he] at h
    exact h
  · simpa [hij] using (Interval.singleton_mem (0:ℚ))

/-- Trial coordinates as integers in units of 1/1000 of a period. -/
def trialTick : Fin 6 → ℕ := ![0,125,126,250,500,750]

private theorem trialTick_spec : ∀ i, Root22.witnessX i = (trialTick i : ℚ)/1000 := by
  intro i
  fin_cases i <;> norm_num [Root22.witnessX, trialTick]

private theorem trialTick_order : ∀ i j : Fin 6, i < j → trialTick i ≤ trialTick j ∧
    trialTick j < 1000 := by decide

def witnessFrom (node : Order → ℕ → Interval) : Interval :=
  isum univ fun i : Fin 6 => isum univ fun j : Fin 6 =>
    if i < j then
      (Interval.singleton (blockSign i.val j.val)).mul
        (node .value ((trialTick j - trialTick i)*32))
    else .singleton 0

theorem witnessFrom_sound {node : Order → ℕ → Interval}
    (hn : ∀ o p, p < 32000 → (node o p).Mem (mode (orderIndex o) ((p:ℝ)/32000))) :
    (witnessFrom node).Mem (pairScore 22 fun i => (Root22.witnessX i : ℝ)) := by
  apply isum_mem; intro i _
  apply isum_mem; intro j _
  by_cases hij : i < j
  · simp only [hij, if_true]
    have hs : (blockSign i.val j.val : ℝ) = charge i * charge j := by
      simp [blockSign, charge, pow_add]
    rw [← hs]
    apply Interval.mul_mem (Interval.singleton_mem _)
    obtain ⟨hle, hlt⟩ := trialTick_order i j hij
    have hp : (trialTick j - trialTick i)*32 < 32000 := by omega
    have h := hn .value _ hp
    have he : ((trialTick j - trialTick i)*32 : ℕ)/(32000:ℝ) =
        (Root22.witnessX j : ℝ) - (Root22.witnessX i : ℝ) := by
      rw [trialTick_spec j, trialTick_spec i]
      push_cast [Nat.cast_sub hle]
      ring
    rw [he] at h
    exact h
  · simpa [hij] using (Interval.singleton_mem (0:ℚ))

end GaussianChains.Point22.Atlas
