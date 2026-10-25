/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Instance.Combinatorics.RestrictedGaussianPartition.Part2


namespace MetaMathlibExt

/-- Adjacent-level linkage only: each consecutive pair shares the left dimension
and satisfies the count bound. Zipping with the tail relates consecutive levels,
unlike `List.Pairwise`, which would relate every later pair. -/
def ChainAdjValid (ch : List BranchStep) : Prop :=
  ((ch.zip ch.tail).all (fun p =>
    decide (p.2.a + p.2.b = p.1.a ∧ 1 ≤ p.2.b ∧ p.2.b ≤ p.2.a ∧
      1 ≤ p.2.c ∧ p.2.c ≤ p.1.c)) = true)

end MetaMathlibExt
