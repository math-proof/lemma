/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WeightedAffinePowerSum.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
open scoped BigOperators


namespace MetaMathlibExt

/-!
# Weighted affine power sums

Source: M. D. Schmidt, *Jacobi-Type Continued Fractions for the Ordinary Generating Functions
of Generalized Factorial Functions*, Journal of Integer Sequences 20 (2017),
[`schmidt14.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL20/Schmidt/schmidt14.tex).
-/

/-- The finite sum `S_p(a,b;u,n+1) = ∑_{k=0}^n u^k (ak+b)^p`.

Unlike later generating-function identities in the source, this finite definition does not
require `u` to be nonzero. -/
def weightedAffinePowerSum {R : Type*} [Ring R]
    (a b : ℤ) (u : R) (n p : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), u ^ k * ((a : R) * (k : R) + (b : R)) ^ p

end MetaMathlibExt
