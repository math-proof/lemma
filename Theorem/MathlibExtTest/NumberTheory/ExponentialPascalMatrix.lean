/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ExponentialPascalMatrix.lean -/


import Def.NumberTheory.ExponentialPascalMatrix


namespace MetaMathlibExt

example {R : Type*} [CommRing R] [Algebra ℚ R] (r : ℚ) :
    (exponentialPascalTypePair R r).1 = PowerSeries.exp R := rfl

example {R : Type*} [CommRing R] [Algebra ℚ R] (r : ℚ) :
    (exponentialPascalTypePair R r).2 =
      PowerSeries.X + PowerSeries.C (algebraMap ℚ R (r / 2)) * PowerSeries.X ^ 2 := rfl

example (r : ℚ) : exponentialPascalTypeMatrix ℚ r 0 0 = 1 := by
  simp [exponentialPascalTypeMatrix]

example : exponentialPascalTypeMatrix ℚ 1 2 1 = 3 := by
  norm_num [exponentialPascalTypeMatrix, exponentialPascalTypeSeries, PowerSeries.coeff_mul,
    PowerSeries.coeff_X, Finset.Nat.antidiagonal_succ]

example : exponentialPascalTypeMatrix ℚ 2 2 1 = 4 := by
  norm_num [exponentialPascalTypeMatrix, exponentialPascalTypeSeries, PowerSeries.coeff_mul,
    PowerSeries.coeff_X, Finset.Nat.antidiagonal_succ]

#print axioms MetaMathlibExt.exponentialPascalTypeSeries
#print axioms MetaMathlibExt.exponentialPascalTypePair
#print axioms MetaMathlibExt.exponentialPascalTypeMatrix

end MetaMathlibExt
