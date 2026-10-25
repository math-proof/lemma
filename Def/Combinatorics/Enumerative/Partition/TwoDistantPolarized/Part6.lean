/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part5


namespace MetaMathlibExt.TwoDistantPolarized

open List

def evenP (b : List ℕ) : List ℕ := b.filter (fun x => decide (x % 2 = 0))

def oddP (b : List ℕ) : List ℕ := b.filter (fun x => !decide (x % 2 = 0))

def polyParts (b : List ℕ) : List ℕ :=
  fromB (evenP b) ++ Qof (evenP b).length (oddP b)

end MetaMathlibExt.TwoDistantPolarized
