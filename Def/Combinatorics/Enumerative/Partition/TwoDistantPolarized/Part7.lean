/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part6


namespace MetaMathlibExt.TwoDistantPolarized

open List

def toBoff (j : ℕ) (Q : List ℕ) : List ℕ := Q.mapIdx (fun s x => x - (2*(j+s)+1))

end MetaMathlibExt.TwoDistantPolarized
