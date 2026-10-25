/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LabosPrime.lean -/

import Mathlib.NumberTheory.PrimeCounting
/-!
# Labos primes

This file formalizes Definition 2 from Vladimir Shevelev,
*Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>.
-/


namespace MetaMathlibExt

/-- `IsLabosPrime n L` says that `L` is the least positive integer satisfying
`π(L) - π(L / 2) = n`, for `n ≥ 1`. -/
def IsLabosPrime (n L : ℕ) : Prop :=
  1 ≤ n ∧ 0 < L ∧ Nat.primeCounting L - Nat.primeCounting (L / 2) = n ∧
    ∀ m, 0 < m → m < L → Nat.primeCounting m - Nat.primeCounting (m / 2) ≠ n

end MetaMathlibExt
