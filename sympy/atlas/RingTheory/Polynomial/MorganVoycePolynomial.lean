/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/MorganVoycePolynomial.lean -/

import Mathlib.Algebra.Polynomial.Basic

/-!
# Morgan-Voyce polynomials

Formalizes the Morgan-Voyce polynomial family (OEIS A085478) whose coefficient
array is the Riordan array `(1 / (1 - x), x / (1 - x) ^ 2)`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Brietzke/bri3.tex>.
-/

namespace MetaMathlibExt

/-- Morgan-Voyce coefficient array entry `d(n, k)`: `binom{n + k}{n - k}` for
`k ≤ n` and `0` otherwise, giving the lower-triangular Riordan array
`(1 / (1 - x), x / (1 - x) ^ 2)` identified as OEIS A085478.
Source statement `jis_9df126595a4035315bd915ac`,
concept `jis_sem_455f7ec0e8ec92a0f271843b`. -/
def morganVoyceCoeff (n k : ℕ) : ℕ :=
  if k ≤ n then (n + k).choose (n - k) else 0

/-- Morgan-Voyce polynomial of index `n`: the polynomial whose coefficients are
the entries `d(n, k)` of the Riordan array `(1 / (1 - x), x / (1 - x) ^ 2)`.
Source statement `jis_9df126595a4035315bd915ac`,
concept `jis_sem_455f7ec0e8ec92a0f271843b` (OEIS A085478). -/
noncomputable def morganVoycePolynomial (R : Type*) [Semiring R] (n : ℕ) :
    Polynomial R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    Polynomial.C ((morganVoyceCoeff n k : ℕ) : R) * Polynomial.X ^ k

end MetaMathlibExt
