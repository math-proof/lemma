/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized


namespace MetaMathlibExt.TwoDistantPolarized

open List

-- sorted parts list of a partition
noncomputable def sl {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≤ ·)

end MetaMathlibExt.TwoDistantPolarized
