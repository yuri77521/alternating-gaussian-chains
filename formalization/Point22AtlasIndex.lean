import CertTree
import Point22Contacts

/-! Integer interval claims are inert records. Lookup checks the complete key before
the interval can be used, and a successful lookup always returns an actual member. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

def packKey (a b o l r : ℕ) := (((a*7+b)*3+o)*32001+l)*32001+r

def ofTicks (lo hi : ℤ) : Interval := ⟨lo / (10^11 : ℚ), hi / (10^11 : ℚ)⟩

structure RangeClaim where
  a : ℕ
  b : ℕ
  ord : ℕ
  L : ℕ
  R : ℕ
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

inductive RangeIndex
  | leaf (row : RangeClaim)
  | fork (pivot : ℕ) (left right : RangeIndex)

namespace RangeIndex

def entries : RangeIndex → List RangeClaim
  | .leaf r => [r]
  | .fork _ l r => l.entries ++ r.entries

def find (index : RangeIndex) (key : ℕ) : RangeClaim :=
  match index with
  | .leaf r => r
  | .fork pivot l r => if key ≤ pivot then l.find key else r.find key

theorem find_mem (index : RangeIndex) (key : ℕ) : index.find key ∈ index.entries := by
  induction index with
  | leaf r => simp [find,entries]
  | fork p l r il ir =>
    by_cases h : key ≤ p
    · simp [find, entries, h, il]
    · simp [find, entries, h, ir]

def find? (index : RangeIndex) (a b o l r : ℕ) : Option RangeClaim :=
  let row := index.find (packKey a b o l r)
  if row.a=a ∧ row.b=b ∧ row.ord=o ∧ row.L=l ∧ row.R=r then some row else none

theorem find?_spec {idx : RangeIndex} {a b o l r : ℕ} {c : RangeClaim}
    (h : idx.find? a b o l r = some c) :
    c ∈ idx.entries ∧ c.a=a ∧ c.b=b ∧ c.ord=o ∧ c.L=l ∧ c.R=r := by
  unfold find? at h
  dsimp only at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨idx.find_mem _, by assumption⟩
  · contradiction

end RangeIndex
end GaussianChains.Point22.Atlas
