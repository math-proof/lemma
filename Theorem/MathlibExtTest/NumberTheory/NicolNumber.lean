/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean -/
module

public import Def.NumberTheory.NicolNumber
public import Theorem.Nat.NicolNumber
open MetaMathlibExt
open scoped BigOperators

public section

example : IsNicolNumber 1 :=
  test_t_nicol_two_one.isNicolNumber

