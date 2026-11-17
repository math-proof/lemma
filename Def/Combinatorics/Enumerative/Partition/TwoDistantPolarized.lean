/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt.TwoDistantPolarized

open List

def fromB (b : List ℕ) : List ℕ := b.mapIdx (fun i x => x + (2*i+1))

def toB (L : List ℕ) : List ℕ := L.mapIdx (fun i x => x - (2*i+1))

end MetaMathlibExt.TwoDistantPolarized
