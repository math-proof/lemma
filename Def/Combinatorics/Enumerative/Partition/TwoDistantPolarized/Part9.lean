module
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/
namespace MetaMathlibExt.TwoDistantPolarized

open List

noncomputable def invB {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  ((↑(toB (Pl p)) + ↑(toBoff (Pl p).length (Ql p)) : Multiset ℕ)).sort (· ≤ ·)

end MetaMathlibExt.TwoDistantPolarized
