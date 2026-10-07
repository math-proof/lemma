import sympy.functions.combinatorial.numbers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset

/-! Facts about `Stirling.conditionset` (ordered set partitions): blocks lie in `range n`, distinct blocks
are disjoint, the `s0_B` / `s2_A` / `s2_B` decompositions, and the identification of the number of
unordered partitions with Mathlib's `Nat.stirlingSecond` via the recurrence.
-/

namespace Stirling.conditionset


/-- The set of (unordered) partitions of `range n` into `k` blocks, as block sets of ordered partitions. -/
abbrev parts (n k : ℕ) : Set (Finset (Finset ℕ)) :=
  (fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k

end Stirling.conditionset
