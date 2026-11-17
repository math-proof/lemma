/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GaleRyser.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MathlibExt.Combinatorics.GaleRyserWanted

/-! # Gale–Ryser theorem -/

/-- Prefix sum of `r` over first `k` entries. -/
def prefixSum {m : ℕ} (r : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if h : i < m then r ⟨i, h⟩ else 0

/-- Tail of a row-sum sequence (drop the first row). -/
def tailRow {m : ℕ} (r : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun i => r i.succ

/-- Decrement the first `e` column sums by one. -/
def decCol {n : ℕ} (c : Fin n → ℕ) (e : ℕ) : Fin n → ℕ :=
  fun j => if j.val < e then c j - 1 else c j

end MathlibExt.Combinatorics.GaleRyserWanted
end
