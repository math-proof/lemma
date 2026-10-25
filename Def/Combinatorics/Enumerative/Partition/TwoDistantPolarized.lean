/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring


namespace MetaMathlibExt.TwoDistantPolarized

open List

def fromB (b : List ℕ) : List ℕ := b.mapIdx (fun i x => x + (2*i+1))

def toB (L : List ℕ) : List ℕ := L.mapIdx (fun i x => x - (2*i+1))

end MetaMathlibExt.TwoDistantPolarized
