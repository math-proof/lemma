/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow


namespace MetaMathlibExt

/-- A Gaussian partition type, represented by its nonincreasing list of
subspace dimensions. This small carrier is kept local to the substantive
restricted-Gaussian-partition development rather than published as a
standalone entry. -/
structure GaussianPartition where
  dims : List ℕ
  sorted_desc : List.Pairwise (· ≥ ·) dims

/-- A descending block `(d, m)` of an integer partition of `n`. -/
structure Block where
  d : Nat
  m : Nat
deriving DecidableEq, Repr

/-- One simultaneous split level: `c` copies of parent `a + b` become `c` copies
of `a` and `c * q ^ a` copies of `b`. -/
structure BranchStep where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, Repr

end MetaMathlibExt
