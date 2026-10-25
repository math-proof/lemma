/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part2


namespace MetaMathlibExt.TwoDistantPolarized

open List

-- build a partition from a list
def ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n) :
    Nat.Partition n where
  parts := (L : Multiset ℕ)
  parts_pos := by intro i hi; exact hpos i (by simpa using hi)
  parts_sum := by simpa using hsum

end MetaMathlibExt.TwoDistantPolarized
