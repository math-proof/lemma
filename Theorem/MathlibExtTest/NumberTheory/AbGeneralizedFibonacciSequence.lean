/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AbGeneralizedFibonacciSequence.lean -/


import Structure.NumberTheory.AbGeneralizedFibonacciSequence
import Lemma.Nat.AbGeneralizedFibonacciSequence
import Def.MathlibExtTest.NumberTheory.AbGeneralizedFibonacciSequence


namespace MetaMathlibExt

example : impulseGeneralizedFibonacci.F 0 = 0 :=
  impulseGeneralizedFibonacci.initial_zero

example : impulseGeneralizedFibonacci.F 1 = 1 :=
  impulseGeneralizedFibonacci.initial_one

example (n : ℕ) : impulseGeneralizedFibonacci.F (n + 2) =
    impulseGeneralizedFibonacci.a * impulseGeneralizedFibonacci.F (n + 1) +
      impulseGeneralizedFibonacci.b * impulseGeneralizedFibonacci.F n :=
  impulseGeneralizedFibonacci.recurrence n

example :
    (1 - PowerSeries.C impulseGeneralizedFibonacci.a * PowerSeries.X -
      PowerSeries.C impulseGeneralizedFibonacci.b * PowerSeries.X ^ 2) *
      PowerSeries.mk impulseGeneralizedFibonacci.F = PowerSeries.X :=
  impulseGeneralizedFibonacci.gen_eq

example (x y : AbGeneralizedFibonacciSequence)
    (ha : x.a = y.a) (hb : x.b = y.b) (hF : x.F = y.F) : x = y := by
  ext
  · exact ha
  · exact hb
  · exact congrFun hF _

end MetaMathlibExt
