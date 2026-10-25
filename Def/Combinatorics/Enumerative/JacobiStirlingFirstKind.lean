/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Coeff
open scoped BigOperators


namespace MetaMathlibExt

/-- N-th first-kind Jacobi-Stirling generating polynomial over a commutative ring,
the product over `i < n` of `X - C (i * (i + ζ))`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
noncomputable def jacobiStirlingFirstPoly {R : Type*} [CommRing R]
    (n : ℕ) (ζ : R) : Polynomial R :=
  ∏ i ∈ Finset.range n,
    (Polynomial.X - Polynomial.C ((i : R) * ((i : R) + ζ)))

/-- First-kind Jacobi-Stirling numbers `J(n,k;ζ)`, defined as the coefficient
of `X^k` in the generating polynomial.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
noncomputable def jacobiStirlingFirst {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) : R :=
  (jacobiStirlingFirstPoly n ζ).coeff k

end MetaMathlibExt
