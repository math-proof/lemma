/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized

@[expose] public section

namespace MetaMathlibExt.TwoDistantPolarized

open List

-- sorted parts list of a partition
noncomputable def sl {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≤ ·)

end MetaMathlibExt.TwoDistantPolarized
