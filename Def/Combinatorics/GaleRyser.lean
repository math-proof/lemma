/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GaleRyser.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring


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
