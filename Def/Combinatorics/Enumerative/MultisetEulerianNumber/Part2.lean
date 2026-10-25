/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MultisetEulerianNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Instance.Combinatorics.Enumerative.MultisetEulerianNumber
/-!
# Eulerian numbers of multiset permutations

This file formalizes the descent-count definition in Dzhumadil'daev and
Yeliussizov, *Power Sums of Binomial Coefficients*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>.
-/


namespace MetaMathlibExt

/-- The Eulerian number of multiset permutations with source-convention
descent number `p`.

For multiplicities `2, 2`, its nonzero values are `1, 4, 1` at `p = 1, 2, 3`.
The source concept is `jis_sem_121d1b2b298abdf4f82cc1e3`. -/
def multisetEulerianNumber {m : ℕ} (k : Fin m → ℕ) (p : ℕ) : ℕ :=
  let K := Finset.sum Finset.univ k
  ((Finset.univ : Finset (Fin K → Fin m)).filter fun w =>
    IsMultisetPermutation k w ∧ multisetDescentNumber w = p).card

end MetaMathlibExt
