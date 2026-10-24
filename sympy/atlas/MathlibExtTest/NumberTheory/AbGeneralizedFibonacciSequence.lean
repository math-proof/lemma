/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AbGeneralizedFibonacciSequence.lean -/


import sympy.atlas.NumberTheory.AbGeneralizedFibonacciSequence
import Lemma.Nat.AbGeneralizedFibonacciSequence

namespace MetaMathlibExt

private noncomputable def impulseGeneralizedFibonacci : AbGeneralizedFibonacciSequence where
  a := 0
  b := 0
  F := fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ)
  initial_zero := by simp
  initial_one := by simp
  recurrence := by intro n; simp [PowerSeries.coeff_X]
  gen_eq := by
    simp only [map_zero, zero_mul, sub_zero, one_mul]
    ext n
    simp [PowerSeries.coeff_X]

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
