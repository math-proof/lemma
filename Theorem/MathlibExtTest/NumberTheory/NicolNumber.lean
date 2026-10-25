/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean -/


import Def.NumberTheory.NicolNumber
import Lemma.Nat.NicolNumber
open MetaMathlibExt
open scoped BigOperators


example : IsNicolNumber 1 :=
  test_t_nicol_two_one.isNicolNumber

