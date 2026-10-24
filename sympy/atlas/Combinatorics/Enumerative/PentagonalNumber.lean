/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas

open scoped BigOperators
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

/-- Integer partition function `p(n)`, the number of partitions of `n`,
via `Mathlib` partition card. Stable source:
https://en.wikipedia.org/wiki/Pentagonal_number_theorem
("Pentagonal number theorem", statement `pentagonal-s1`). -/
def partitionFunction (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)
end MetaMathlibExt
