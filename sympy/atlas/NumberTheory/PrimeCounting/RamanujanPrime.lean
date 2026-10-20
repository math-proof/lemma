/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/RamanujanPrime.lean -/

import Mathlib.NumberTheory.PrimeCounting

/-!
# Ramanujan prime

Formalizes the required definition clause for the Ramanujan prime concept
(concept `jis_sem_2ce4a4483a6ae69670d63026`, statement `jis_b3eb662622ec0b548e5acec4`,
source `jis_source_04b544b932aca55da03d6b0c`).

Source: Vladimir Shevelev,
*Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>.
-/

namespace MetaMathlibExt

/-- A prime `R` satisfies the Ramanujan counting condition for `n`, i.e.
`π(R) - π(R / 2) = n`, where `π` is the prime-counting function.

For natural `R`, `π(R / 2)` (primes `p ≤ R / 2` over the reals) agrees with
`Nat.primeCounting (R / 2)` under `Nat` division.
Concept `jis_sem_2ce4a4483a6ae69670d63026`;
statement `jis_b3eb662622ec0b548e5acec4`. -/
def IsRamanujanPrime (R n : ℕ) : Prop :=
  Nat.Prime R ∧ (Nat.primeCounting R - Nat.primeCounting (R / 2) = n)

/-- For `n ≥ 1`, `R` is the `n`-th Ramanujan prime: the largest prime with
`π(R) - π(R / 2) = n`.
Concept `jis_sem_2ce4a4483a6ae69670d63026`;
statement `jis_b3eb662622ec0b548e5acec4`. -/
def IsNthRamanujanPrime (R n : ℕ) : Prop :=
  1 ≤ n ∧ IsRamanujanPrime R n ∧ ∀ p : ℕ, IsRamanujanPrime p n → p ≤ R

end MetaMathlibExt
