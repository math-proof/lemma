/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimitiveDivisor.lean -/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Def.NumberTheory.PrimitiveDivisor
public import Theorem.Nat.PrimitiveDivisor

@[expose] public section

namespace IntegerSequence

def testSeq : ℕ → ℤ
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | _ => 0

end IntegerSequence
