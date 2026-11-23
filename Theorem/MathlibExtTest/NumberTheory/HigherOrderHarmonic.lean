/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HigherOrderHarmonic.lean -/
module

public import Def.NumberTheory.HigherOrderHarmonic
public import Theorem.Nat.HigherOrderHarmonic

public section

example : higherHarmonic 0 2 = 0 :=
  higherHarmonic_zero 2

example : higherHarmonic 1 2 = 1 :=
  higherHarmonic_one 2

example : higherHarmonic (1 + 1) 2 =
    higherHarmonic 1 2 + (1 : Rat) / ((((1 + 1 : Nat)) : Rat) ^ 2) :=
  higherHarmonic_succ 1 2

example : higherHarmonic 2 1 = harmonic 2 :=
  higherHarmonic_order_one 2

