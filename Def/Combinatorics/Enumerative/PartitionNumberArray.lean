/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionNumberArray.lean -/

import Mathlib.Data.Nat.Factorial.Basic
/-!
# Partition number array (concept jis_sem_4bcead3a4bcda58a1d4dbb9f)
-/


namespace MetaMathlibExt

namespace PartitionNumberArray

/-- Extend an exponent vector to a total index function.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def extendA (n : Nat) (a : Fin n → Nat) (j : Nat) : Nat :=
  if h : j < n then a ⟨j, h⟩ else 0

/-- Weighted-sum recursion helper.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def weightSumAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => weightSumAux n f + (n + 1) * f n

/-- Part-count recursion helper.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def countSumAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => countSumAux n f + f n

/-- Weighted part-size sum of an exponent vector.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def multWeightSum (n : Nat) (a : Fin n → Nat) : Nat :=
  weightSumAux n (extendA n a)

/-- Total part count of an exponent vector.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def countSum (n : Nat) (a : Fin n → Nat) : Nat :=
  countSumAux n (extendA n a)

end PartitionNumberArray
end MetaMathlibExt
