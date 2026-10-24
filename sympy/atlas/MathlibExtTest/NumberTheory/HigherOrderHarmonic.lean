/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HigherOrderHarmonic.lean -/


import sympy.atlas.NumberTheory.HigherOrderHarmonic
import Lemma.Nat.HigherOrderHarmonic

#check @higherHarmonic
#check @higherHarmonic_zero
#check @higherHarmonic_succ
#check @higherHarmonic_one
#check @higherHarmonic_order_one

example : higherHarmonic 0 2 = 0 :=
  higherHarmonic_zero 2

example : higherHarmonic 1 2 = 1 :=
  higherHarmonic_one 2

example : higherHarmonic (1 + 1) 2 =
    higherHarmonic 1 2 + (1 : Rat) / ((((1 + 1 : Nat)) : Rat) ^ 2) :=
  higherHarmonic_succ 1 2

example : higherHarmonic 2 1 = harmonic 2 :=
  higherHarmonic_order_one 2
