/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part3


namespace MetaMathlibExt.TwoDistantPolarized

open List

def Omega (n : ℕ) := {L : List ℕ // L.Pairwise (· ≤ ·) ∧ L.sum + L.length ^ 2 = n}

end MetaMathlibExt.TwoDistantPolarized
