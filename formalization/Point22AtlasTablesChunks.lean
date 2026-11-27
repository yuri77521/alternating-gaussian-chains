import Point22AtlasTablesFixed

/-! Certificates for splitting the 128001-sample recurrence. A query only
unfolds the steps inside one block. Every supplied block start is linked to
the preceding start, and the first state is checked against the Taylor seed. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.Cert GaussianChains.Cert.Nodes GaussianChains.ImageBounds

def ValidStarts (width count : ℕ) (starts : ℕ → State) : Prop :=
  starts 0 = init ∧ ∀ b < count, step^[width] (starts b) = starts (b+1)

theorem valid_start_eq {width count : ℕ} {starts : ℕ → State}
    (hc : ValidStarts width count starts) {b : ℕ} (hb : b ≤ count) :
    starts b = step^[b*width] init := by
  induction b with
  | zero => simpa using hc.1
  | succ b ih =>
    rw [← hc.2 b (by omega), ih (by omega), Nat.succ_mul, Nat.add_comm,
      Function.iterate_add_apply]

def sampleFrom (width : ℕ) (starts : ℕ → State) (n : ℕ) : Ticks :=
  (step^[n % width] (starts (n / width))).sample

theorem sampleFrom_eq {width count : ℕ} {starts : ℕ → State}
    (hc : ValidStarts width count starts) {n : ℕ} (hb : n / width ≤ count) :
    (sampleFrom width starts n).decode work = (gaussianEntry work param n).sample := by
  unfold sampleFrom
  rw [valid_start_eq hc hb, ← Function.iterate_add_apply,
    Nat.mul_comm (n / width) width, Nat.mod_add_div]
  exact congrArg Entry.sample (iterate_eq n)

end GaussianChains.Point22.Atlas.Tables

