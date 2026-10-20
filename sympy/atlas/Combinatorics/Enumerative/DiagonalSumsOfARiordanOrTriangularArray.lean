/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DiagonalSumsOfARiordanOrTriangularArray.lean -/

import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped BigOperators

namespace MetaMathlibExt

/-- Diagonal sums of a Riordan or triangular array, summing along rising
antidiagonals of an infinite lower-triangular array `a`.

For a Riordan array `(g, f)` this is the sequence characterized by
`g(x) / (1 - x * f(x))`, e.g. `d_n = ∑ k, a k (n - k)`.

Sources: concept `jis_sem_c3bf1fb2d96732b9f14d51d2`
(`diagonal sums of a Riordan or triangular array`);
statements `jis_1fa1c63beb99b6d942ce3fe3`, `jis_4b608c30d02bc9d0bb18b1ad`,
`jis_509208625b436fe419d6aa27`, `jis_75a2bcc65150b23df74aa083`,
`jis_799c84fba972a9e02b813f68`, `jis_8ac1daf4464d5f9b03e74e04`,
`jis_9694b3ddf1cac31314a02552`, `jis_cde4fe6dab53c64bf1efc7ff`,
`jis_da460a82515493c122167fec`. -/
def diagonalSums {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ → M) (n : ℕ) : M :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 ij.2

end MetaMathlibExt
