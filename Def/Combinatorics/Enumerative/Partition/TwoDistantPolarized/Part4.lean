/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part3

@[expose] public section

namespace MetaMathlibExt.TwoDistantPolarized

open List

def Omega (n : ℕ) := {L : List ℕ // L.Pairwise (· ≤ ·) ∧ L.sum + L.length ^ 2 = n}

end MetaMathlibExt.TwoDistantPolarized
