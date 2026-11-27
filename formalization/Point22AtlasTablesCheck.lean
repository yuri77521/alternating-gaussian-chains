import Point22AtlasTablesChunks

/-! Kernel-checkable, independent chunks. Each stream certificate validates all
its published samples and its outgoing state. Adjacent chunks share that state. -/
namespace GaussianChains.Point22.Atlas.Tables

open GaussianChains.Cert.Nodes

def checkBand (values : ℕ → Ticks) (stop : State) : ℕ → ℕ → State → Bool
  | 0, _, st => decide (st = stop)
  | k+1, n, st => decide (values n = st.sample) && checkBand values stop k (n+1) (step st)

theorem checkBand_spec {values : ℕ → Ticks} {stop : State} (len : ℕ) (n : ℕ) (st : State)
    (h : checkBand values stop len n st = true) :
    (∀ i < len, values (n+i) = (step^[i] st).sample) ∧ step^[len] st = stop := by
  induction len generalizing n st with
  | zero => simpa [checkBand] using h
  | succ len ih =>
    obtain ⟨h₀,h₁⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,hb⟩ := ih (n+1) (step st) h₁
    constructor
    · intro i hi
      cases i with
      | zero => simpa using (of_decide_eq_true h₀)
      | succ i =>
        rw [Function.iterate_succ_apply, show n+(i+1) = n+1+i by omega]
        exact ha i (by omega)
    · rwa [Function.iterate_succ_apply]

def Checked (f : ℕ → Bool) (lo hi : ℕ) := ∀ i, lo ≤ i → i < hi → f i = true

def segmentOK (f : ℕ → Bool) (lo count : ℕ) := (List.range count).all (fun k => f (lo+k))

theorem Checked.of_segment {f : ℕ → Bool} {lo count : ℕ} (h : segmentOK f lo count = true) :
    Checked f lo (lo+count) := by
  intro i hli hhi
  have hsub : i-lo ∈ List.range count := List.mem_range.mpr (by omega)
  have h' := List.all_eq_true.mp h _ hsub
  change f (lo+(i-lo)) = true at h'
  rwa [show lo+(i-lo) = i by omega] at h'

theorem Checked.join {f : ℕ → Bool} {lo mid hi : ℕ} (h₁ : Checked f lo mid) (h₂ : Checked f mid hi) :
    Checked f lo hi := by
  intro i h₀ h₃
  by_cases hm : i < mid
  · exact h₁ i h₀ hm
  · exact h₂ i (by omega) h₃

def bandOK (values : ℕ → Ticks) (starts : ℕ → State) (b : ℕ) :=
  checkBand values (starts (b+1)) 64 (b*64) (starts b)

theorem checkedSamples_eq {values : ℕ → Ticks} {starts : ℕ → State}
    (hvalid : Checked (bandOK values starts) 0 2000) (h0 : starts 0 = init)
    (hend : values 128000 = (starts 2000).sample)
    {n : ℕ} (hn : n ≤ 128000) :
    (values n).decode work = (gaussianEntry work param n).sample := by
  have hs (b : ℕ) (hb : b < 2000) := checkBand_spec 64 (b*64) (starts b)
    (hvalid b (Nat.zero_le _) hb)
  have hv : ValidStarts 64 2000 starts := ⟨h0,fun b hb => (hs b hb).2⟩
  have he : values n = sampleFrom 64 starts n := by
    by_cases hl : n = 128000
    · subst n
      exact hend
    · have hb : n/64 < 2000 := by omega
      have ha := (hs (n/64) hb).1 (n%64) (by omega)
      rwa [show n/64*64+n%64 = n by omega] at ha
  rw [he]
  exact sampleFrom_eq hv (by omega)

end GaussianChains.Point22.Atlas.Tables

