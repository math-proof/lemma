/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HigherOrderHarmonic.lean -/


import Def.NumberTheory.HigherOrderHarmonic
import Lemma.Nat.HigherOrderHarmonic


example : higherHarmonic 0 2 = 0 :=
  higherHarmonic_zero 2

example : higherHarmonic 1 2 = 1 :=
  higherHarmonic_one 2

example : higherHarmonic (1 + 1) 2 =
    higherHarmonic 1 2 + (1 : Rat) / ((((1 + 1 : Nat)) : Rat) ^ 2) :=
  higherHarmonic_succ 1 2

example : higherHarmonic 2 1 = harmonic 2 :=
  higherHarmonic_order_one 2

