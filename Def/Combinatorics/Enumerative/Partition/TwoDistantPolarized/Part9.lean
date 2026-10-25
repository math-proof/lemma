/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part8


namespace MetaMathlibExt.TwoDistantPolarized

open List

noncomputable def invB {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  ((↑(toB (Pl p)) + ↑(toBoff (Pl p).length (Ql p)) : Multiset ℕ)).sort (· ≤ ·)

end MetaMathlibExt.TwoDistantPolarized
