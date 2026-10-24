/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean -/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.PerfectPairing.Basic

open Module

/-!
# Dual bases for perfect pairings

Given a perfect pairing `B : M →ₗ[A] N →ₗ[A] A` between `A`-modules `M`
and `N`, and a basis `b` of `N` indexed by a finite decidable type, the
canonical left dual basis is obtained by transporting the ordinary dual
basis along the inverse of the pairing equivalence.

## Main definitions

* `LinearMap.IsPerfPair.dualBasis`: the canonical left dual basis,
  `b.dualBasis.map B.toPerfPair.symm`.

## Main results

* `LinearMap.IsPerfPair.dualBasis_apply`: evaluation formula
  `B (dualBasis B b i) (b j) = if j = i then 1 else 0`.
* `LinearMap.IsPerfPair.eq_dualBasis_of`: uniqueness of any basis
  satisfying that formula.
* `LinearMap.IsPerfPair.exists_dualBasis` and
  `LinearMap.IsPerfPair.existsUnique_dualBasis`: existence and unique
  existence wrappers.
-/

namespace LinearMap.IsPerfPair

variable {A M N ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]
variable [DecidableEq ι] [Finite ι]
variable (B : M →ₗ[A] N →ₗ[A] A) [B.IsPerfPair]

/-- The canonical left dual basis of `b` with respect to the perfect pairing
`B`: transport the ordinary dual basis `b.dualBasis` along the inverse of
the pairing equivalence `B.toPerfPair`. -/
noncomputable def dualBasis (b : Basis ι A N) : Basis ι A M :=
  b.dualBasis.map B.toPerfPair.symm
end LinearMap.IsPerfPair
