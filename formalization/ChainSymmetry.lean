import ChainScore
import ChainGeometry

/-! # Energy symmetries of a labeled alternating cell

Translation, reflection and choice of a lift are symmetries of the potential.
An even cyclic relabeling preserves species, while an odd relabeling changes
every charge by the same sign. Both operations preserve the pair products.
-/

namespace GaussianChains

noncomputable section

theorem imageEnergy_translate {N : ℕ} (s t : ℝ) (x : Fin N → ℝ) :
    imageEnergy s (fun i => x i + t) = imageEnergy s x := by
  simp [imageEnergy]

theorem imageEnergy_reflect {N : ℕ} (s : ℝ) (x : Fin N → ℝ) :
    imageEnergy s (fun i => -x i) = imageEnergy s x := by
  unfold imageEnergy
  have h (i j : Fin N) : -x j - -x i = -(x j - x i) := by ring
  simp_rw [h, kernel_neg]

/-- Independent integer shifts change representatives but not their circle points. -/
theorem imageEnergy_add_lifts {N : ℕ} (s : ℝ) (x : Fin N → ℝ) (k : Fin N → ℤ) :
    imageEnergy s (fun i => x i + (k i : ℝ)) = imageEnergy s x := by
  unfold imageEnergy
  have h (i j : Fin N) :
      x j + (k j : ℝ) - (x i + (k i : ℝ)) = (x j - x i) + ((k j - k i : ℤ) : ℝ) := by
    push_cast
    ring
  simp_rw [h, kernel_add_int]

/-- This identity applies whenever the permutation preserves *pair products*.
It does not identify the two species as a geometric equivalence. -/
theorem imageEnergy_relabel {N : ℕ} (s : ℝ) (x : Fin N → ℝ) (p : Equiv.Perm (Fin N))
    (hp : ∀ i j, charge i * charge j = charge (p i) * charge (p j)) :
    imageEnergy s (fun i => x (p i)) = imageEnergy s x := by
  unfold imageEnergy
  apply congrArg (fun S : ℝ => 1 - (1 / (N : ℝ)) * S)
  apply Fintype.sum_equiv p
  intro i
  apply Fintype.sum_equiv p
  intro j
  rw [hp i j]

theorem charge_cyclic_add {N : ℕ} (hN : 2 ∣ N) (i t : Fin N) :
    charge (i+t) = charge i * charge t := by
  unfold charge
  rw [← pow_add, Fin.val_add, neg_one_pow_eq_pow_mod_two ((i.val + t.val) % N),
    Nat.mod_mod_of_dvd _ hN, ← neg_one_pow_eq_pow_mod_two]

theorem even_shift_preserves_species {N : ℕ} (hN : 2 ∣ N) (t : Fin N) (ht : Even t.val)
    (i : Fin N) : charge (i+t) = charge i := by
  have ht' : charge t = 1 := ht.neg_one_pow
  rw [charge_cyclic_add hN, ht', mul_one]

theorem odd_shift_reverses_species {N : ℕ} (hN : 2 ∣ N) (t : Fin N) (ht : Odd t.val)
    (i : Fin N) : charge (i+t) = -charge i := by
  rw [charge_cyclic_add hN]
  have ht' : charge t = -1 := ht.neg_one_pow
  rw [ht', mul_neg_one]

theorem imageEnergy_cyclicShift {N : ℕ} [NeZero N] (hN : 2 ∣ N) (s : ℝ)
    (x : Fin N → ℝ) (t : Fin N) :
    imageEnergy s (fun i => x (i+t)) = imageEnergy s x := by
  apply imageEnergy_relabel s x (Equiv.addRight t)
  intro i j
  change charge i * charge j = charge (i+t) * charge (j+t)
  rw [charge_cyclic_add hN, charge_cyclic_add hN]
  calc
    _ = charge i * charge j * (charge t * charge t) := by rw [charge_mul_self, mul_one]
    _ = _ := by ring

/-- Recut the ordered lifts at label `t`, continuing into the next period
when the list wraps. The bare permutation of representatives need not be ordered. -/
def shiftLifts {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (t i : Fin N) : ℝ :=
  liftSite hN x (i.val + t.val)

theorem liftSite_shiftLifts {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (t : Fin N) (n : ℕ) :
    liftSite hN (shiftLifts hN x t) n = liftSite hN x (n+t.val) := by
  have h : n + t.val = (n % N + t.val) + N * (n / N) := by
    have := Nat.mod_add_div n N
    omega
  rw [h, liftSite_add_periods]
  rfl

theorem gap_shiftLifts {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (t i : Fin N) :
    gap hN (shiftLifts hN x t) i = gap hN x (i+t) := by
  rw [gap_eq_lift_sub, liftSite_shiftLifts, liftSite_shiftLifts,
    show i.val + 1 + t.val = i.val + t.val + 1 by omega, gap_lift_period]
  rfl

theorem feasible_shiftLifts_iff {N : ℕ} [NeZero N] (hN : 0 < N) (h : ℝ)
    (x : Fin N → ℝ) (t : Fin N) : Feasible hN h (shiftLifts hN x t) ↔ Feasible hN h x := by
  constructor
  · intro hx i
    obtain ⟨j, rfl⟩ := (Equiv.addRight t).surjective i
    exact (gap_shiftLifts hN x t j) ▸ hx j
  · intro hx i
    rw [gap_shiftLifts]
    exact hx (i+t)

theorem imageEnergy_shiftLifts {N : ℕ} [NeZero N] (hN : 0 < N) (heven : 2 ∣ N)
    (s : ℝ) (x : Fin N → ℝ) (t : Fin N) :
    imageEnergy s (shiftLifts hN x t) = imageEnergy s x := by
  let k (i : Fin N) : ℤ := ((i.val + t.val) / N : ℕ)
  have hk : shiftLifts hN x t = fun i => x (i+t) + (k i : ℝ) := by
    funext i
    simp only [shiftLifts, liftSite, k, Int.cast_natCast]
    rfl
  rw [hk, imageEnergy_add_lifts s (fun i => x (i+t)) k, imageEnergy_cyclicShift heven]

/-- Reversing the order of labels about label zero preserves species. -/
theorem charge_reverse {N : ℕ} [NeZero N] (hN : 2 ∣ N) (i : Fin N) :
    charge (-i) = charge i := by
  calc
    _ = charge (-i) * (charge i * charge i) := by rw [charge_mul_self, mul_one]
    _ = charge (-i+i) * charge i := by rw [charge_cyclic_add hN]; ring
    _ = charge i := by simp [charge]

theorem imageEnergy_orderedReflection {N : ℕ} [NeZero N] (hN : 2 ∣ N) (s : ℝ)
    (x : Fin N → ℝ) :
    imageEnergy s (fun i => -x (-i)) = imageEnergy s x := by
  rw [imageEnergy_reflect s (fun i => x (-i))]
  apply imageEnergy_relabel s x (Equiv.neg (Fin N))
  intro i j
  simp only [Equiv.neg_apply, charge_reverse hN]

/-- Ordered real lifts of the reflection about label zero. The central label
is represented one period earlier so that the last gap also has the right sign. -/
def reflectLifts {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  -liftSite hN x (N-i.val)

theorem gap_reflectLifts {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) :
    gap hN (reflectLifts hN x) i = gap hN x i.rev := by
  have hi := i.isLt
  have hr : (N - (i.val + 1)) % N = N - (i.val + 1) :=
    Nat.mod_eq_of_lt (by omega)
  have revIdx : (⟨(N - (i.val + 1)) % N, Nat.mod_lt _ hN⟩ : Fin N) = i.rev :=
    Fin.ext hr
  rw [← revIdx, ← gap_lift_period]
  by_cases h : i.val + 1 < N
  · rw [gap_interior _ _ _ h]
    change -liftSite hN x (N - (i.val + 1)) - -liftSite hN x (N - i.val) = _
    rw [show N - i.val = N - (i.val + 1) + 1 by omega]
    ring
  · have he : i.val + 1 = N := by omega
    rw [gap_wrap _ _ _ he]
    change -liftSite hN x (N - 0) + 1 - -liftSite hN x (N-i.val) = _
    have hp := liftSite_add_period hN x 0
    rw [Nat.zero_add] at hp
    rw [Nat.sub_zero, hp, he, Nat.sub_self, show N - i.val = 1 by omega]
    ring

theorem feasible_reflectLifts_iff {N : ℕ} (hN : 0 < N) (h : ℝ) (x : Fin N → ℝ) :
    Feasible hN h (reflectLifts hN x) ↔ Feasible hN h x := by
  constructor
  · intro hx i
    simpa only [gap_reflectLifts, Fin.rev_rev] using hx i.rev
  · intro hx i
    rw [gap_reflectLifts]
    exact hx i.rev

theorem imageEnergy_reflectLifts {N : ℕ} [NeZero N] (hN : 0 < N) (heven : 2 ∣ N)
    (s : ℝ) (x : Fin N → ℝ) : imageEnergy s (reflectLifts hN x) = imageEnergy s x := by
  let k (i : Fin N) : ℤ := -(((N-i.val) / N : ℕ) : ℤ)
  have hk : reflectLifts hN x = fun i => -x (-i) + (k i : ℝ) := by
    funext i
    simp only [reflectLifts, liftSite, Fin.neg_def, k, Int.cast_neg, Int.cast_natCast, neg_add]
  rw [hk, imageEnergy_add_lifts s (fun i => -x (-i)) k, imageEnergy_orderedReflection heven]

end
end GaussianChains
