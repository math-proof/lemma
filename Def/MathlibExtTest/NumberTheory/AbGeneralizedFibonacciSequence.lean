/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AbGeneralizedFibonacciSequence.lean -/


import Structure.NumberTheory.AbGeneralizedFibonacciSequence
import Lemma.Nat.AbGeneralizedFibonacciSequence


namespace MetaMathlibExt

noncomputable def impulseGeneralizedFibonacci : AbGeneralizedFibonacciSequence where
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

end MetaMathlibExt
