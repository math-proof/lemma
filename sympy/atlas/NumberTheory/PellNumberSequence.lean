/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellNumberSequence.lean -/

import Mathlib.Data.Nat.Basic

/-!
# Pell numbers

This module defines the classical Pell number sequence. It is distinct from the parametrized
Pell-equation solution sequences in `Mathlib.NumberTheory.PellMatiyasevic`.

JIS concept: `jis_sem_39440c502b73b93425e3ad17`.
-/

namespace MetaMathlibExt

/-- The Pell numbers `0, 1, 2, 5, 12, …`, defined by
`P_(n+2) = 2 * P_(n+1) + P_n`.

Sources:
* Tian-Xiao He, *Impulse Response Sequences and Construction of Number Sequence Identities*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL16/He/he13.tex>.
* Tian-Xiao He and Peter J.-S. Shiue, *An Approach to the Construction of Linear Divisibility
  Sequences of Higher Orders*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL20/He/he59.tex>.
-/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pellNumber (n + 1) + pellNumber n

end MetaMathlibExt
