/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part4


namespace MetaMathlibExt.TwoDistantPolarized

open List

theorem sl_ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n)
    (hpair : L.Pairwise (· ≤ ·)) : sl (ofList L hpos hsum) = L := by
  rw [sl, ofList_parts, sort_coe_self L hpair]

end MetaMathlibExt.TwoDistantPolarized
