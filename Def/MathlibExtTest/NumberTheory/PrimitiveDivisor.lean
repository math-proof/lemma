/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimitiveDivisor.lean -/


import Mathlib.Data.Nat.Prime.Basic
import Def.NumberTheory.PrimitiveDivisor
import Lemma.Nat.PrimitiveDivisor


namespace IntegerSequence

def testSeq : ℕ → ℤ
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | _ => 0

end IntegerSequence
