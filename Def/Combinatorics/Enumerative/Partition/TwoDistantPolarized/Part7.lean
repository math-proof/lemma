module
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/
namespace MetaMathlibExt.TwoDistantPolarized

open List

def toBoff (j : ℕ) (Q : List ℕ) : List ℕ := Q.mapIdx (fun s x => x - (2*(j+s)+1))

end MetaMathlibExt.TwoDistantPolarized
