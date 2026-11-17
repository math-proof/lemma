/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas

@[expose] public section

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
