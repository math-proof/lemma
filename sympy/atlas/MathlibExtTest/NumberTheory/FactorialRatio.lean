/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FactorialRatio.lean -/


import sympy.atlas.NumberTheory.FactorialRatio
import Lemma.Nat.FactorialRatio

/-!
# Tests for integral factorial ratios

Focused checks for `factorialProd` and `IsIntegralFactorialRatio`: equal
singleton tuples, the `n = 0` boundary, and the central-binomial example
`[(2)] / [(1), (1)]`.
-/


/-- Equal singleton tuples satisfy the predicate. -/
example : IsIntegralFactorialRatio [3] [3] :=
  isIntegralFactorialRatio_singleton_self 3 (by decide)

/-- The `n = 0` boundary: every scaled factorial is one. -/
example : factorialProd [2, 5] 0 = 1 :=
  factorialProd_zero [2, 5]

/-- The `n = 0` divisibility holds for any pair of tuples. -/
example : factorialProd [1, 1] 0 ∣ factorialProd [2] 0 :=
  factorialProd_dvd_zero [2] [1, 1]

/-- Central-binomial example: `[(2)] / [(1), (1)]` is integral. -/
example : IsIntegralFactorialRatio [2] [1, 1] :=
  isIntegralFactorialRatio_centralBinom

/-- Empty tuples satisfy the predicate vacuously. -/
example : IsIntegralFactorialRatio [] [] :=
  isIntegralFactorialRatio_refl [] (fun a ha => by simp at ha)

/-- The balance condition holds on the central example. -/
example : [2].sum = [1, 1].sum :=
  isIntegralFactorialRatio_centralBinom.sum_eq

/-- The divisibility clause fires at every index on the central example. -/
example (n : ℕ) : factorialProd [1, 1] n ∣ factorialProd [2] n :=
  isIntegralFactorialRatio_centralBinom.dvd n

/-- Permuting both tuples preserves the predicate. -/
example : IsIntegralFactorialRatio [2, 1] [2, 1] :=
  isIntegralFactorialRatio_perm (by decide) (by decide)
    (isIntegralFactorialRatio_refl [1, 2] (by decide))
