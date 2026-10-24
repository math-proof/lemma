/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NetoHigherOrderBernoulli.lean -/


import sympy.atlas.NumberTheory.NetoHigherOrderBernoulli
import Lemma.Nat.NetoHigherOrderBernoulli

open MetaMathlibExt

-- Order one recovers the first ordinary Bernoulli number.
example : higherOrderBernoulliNumber 1 1 = (-1 / 2 : ℂ) := by
  rw [higherOrderBernoulliNumber_one, bernoulli_one]
  norm_num

-- Order two gives twice the first ordinary Bernoulli number.
example : higherOrderBernoulliNumber 2 1 = (-1 : ℂ) := by
  change higherOrderBernoulliNumber ((2 : ℕ) : ℂ) 1 = -1
  rw [higherOrderBernoulliNumber_nat]
  simp [pow_two, PowerSeries.coeff_mul, bernoulliPowerSeries, Finset.antidiagonal,
    bernoulli_one]

-- The `n = 1`, `ℓ = 0` case determines the first number from the zeroth.
example (x : ℂ) (h0 : higherOrderBernoulliNumber x 0 = 1) :
    higherOrderBernoulliNumber x 1 = -x / 2 := by
  have h := neto_higher_order_bernoulli_identity x 1 0
  norm_num [Finset.sum_range_succ, h0] at h
  linear_combination h / 2
