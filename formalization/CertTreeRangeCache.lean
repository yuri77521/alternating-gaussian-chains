import CertTreeRanges

/-! A sparse-table implementation of the range specification. Each scale is
built once from the preceding scale; each nonempty query uses two lookups. -/
namespace GaussianChains.Cert.Tables

def getNode (a : Array Interval) (i : ℕ) : Interval := a[i]?.getD ⟨0,0⟩

def nextLevel (a : Array Interval) (j : ℕ) : Array Interval :=
  Array.ofFn fun i : Fin (a.size - 2^j) => hull (getNode a i) (getNode a (i+2^j))

private def row (base : Array Interval) : ℕ → Array Interval
  | 0 => base
  | j+1 => nextLevel (row base j) j

private theorem row_size (base : Array Interval) (j : ℕ) :
    (row base j).size = base.size+1-2^j := by
  induction j with
  | zero => simp [row]
  | succ j ih => simp [row, nextLevel, ih, pow_succ]; omega

private theorem row_correct (base : Array Interval) (j p : ℕ) (hp : p+2^j ≤ base.size) :
    getNode (row base j) p = sparse (getNode base) j p := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    have hp' := hp
    rw [pow_succ] at hp'
    have hr := row_size base j
    have h : p < (row base j).size - 2^j := by omega
    simp only [row, nextLevel, getNode, Array.getElem?_ofFn, h, dite_true,
      Option.getD_some, sparse]
    change hull (getNode (row base j) p) (getNode (row base j) (p+2^j)) = _
    rw [ih _ (by omega), ih _ (by omega)]

def levels (base : Array Interval) : ℕ → Array (Array Interval)
  | 0 => #[base]
  | j+1 =>
    let a := levels base j
    a.push (nextLevel (a[j]?.getD #[]) j)

private theorem levels_size (base : Array Interval) (j : ℕ) : (levels base j).size = j+1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [levels,ih]

private theorem levels_correct (base : Array Interval) (n j : ℕ) (h : j ≤ n) :
    (levels base n)[j]? = some (row base j) := by
  induction n generalizing j with
  | zero => have : j = 0 := by omega
            subst j; rfl
  | succ n ih =>
    rw [levels, Array.getElem?_push, levels_size]
    by_cases hj : j = n+1
    · subst j; simp [ih n le_rfl, row]
    · simp [hj, ih j (by omega)]

/-- The caller can share this value over all boxes of one width and order. -/
def buildRangeCache (nodes : Array Interval) := levels nodes nodes.size.log2

def rangeCached (cache : Array (Array Interval)) (first last : ℕ) : Interval :=
  let j := (last + 1 - first).log2
  let r := cache[j]?.getD #[]
  hull (getNode r first) (getNode r (last + 1 - 2^j))

theorem rangeCached_eq (nodes : Array Interval) {first last : ℕ} (hl : first ≤ last)
    (hr : last < nodes.size) :
    rangeCached (buildRangeCache nodes) first last = rangeHull (getNode nodes) first last := by
  let n := last+1-first
  let j := n.log2
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hv : n + first = last+1 := by dsimp [n]; omega
  have hpow : 2^j ≤ n := Nat.log2_self_le hn
  have hsize : nodes.size ≠ 0 := by omega
  have hj : j ≤ nodes.size.log2 := (Nat.le_log2 hsize).mpr (by omega)
  change hull (getNode (((levels nodes nodes.size.log2)[j]?).getD #[]) first)
    (getNode (((levels nodes nodes.size.log2)[j]?).getD #[]) (last+1-2^j)) = _
  rw [levels_correct nodes nodes.size.log2 j hj, Option.getD_some,
    row_correct nodes j first (by omega), row_correct nodes j (last+1-2^j) (by omega)]
  rfl

end GaussianChains.Cert.Tables
