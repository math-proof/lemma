/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean -/


import Def.NumberTheory.Ramanujan.Part1Ch3Entry14LagrangeSeries
import Lemma.Nat.Ramanujan.Part1Ch3Entry14LagrangeSeries


namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Entry14LagrangeSeries

open scoped BigOperators

open MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14LagrangeSeries

-- The degree-two coefficient reduces to its closed polynomial form.
example (p q n : ℝ) :
    lagrangeSeriesCoefficient p q n 2 = n * (n + 2 * p - q) := by
  rw [lagrangeSeriesCoefficient_of_ne_zero p q n (by norm_num)]
  norm_num

-- Hagen--Rothe remains valid at q = 0.
example (p r s : ℝ) (m : ℕ) :
    lagrangeSeriesCoefficient p 0 (r + s) m =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) *
        lagrangeSeriesCoefficient p 0 r k * lagrangeSeriesCoefficient p 0 s (m - k) := by
  exact lagrangeSeriesCoefficient_add p 0 r s m

-- Hagen--Rothe evaluates the degree-three coefficient at p = 2, q = 1, and n = 3.
example : lagrangeSeriesCoefficient 2 1 3 3 = 168 := by
  rw [← show (1 : ℝ) + 2 = 3 by norm_num]
  calc
    lagrangeSeriesCoefficient 2 1 (1 + 2) 3 =
        ∑ k ∈ Finset.range 4, (Nat.choose 3 k : ℝ) *
          lagrangeSeriesCoefficient 2 1 1 k *
          lagrangeSeriesCoefficient 2 1 2 (3 - k) := by
            simpa using lagrangeSeriesCoefficient_add 2 1 1 2 3
    _ = 168 := by
      norm_num [Finset.sum_range_succ, lagrangeSeriesCoefficient]

-- The boundary value p = 2, q = 1, a = 1/4 gives the Catalan sum at n = 1.
example : ∃ L : ℂ, Complex.exp L = 2 ∧
    HasSum (fun k : ℕ => if k = 0 then (1 : ℂ) else
      (1 : ℂ) * Finset.prod (Finset.range (k - 1))
        (fun j => (1 : ℂ) + (k : ℂ) * (2 : ℂ) - ((j + 1 : ℂ) * (1 : ℂ))) *
          (1 / 4 : ℂ) ^ k / (Nat.factorial k : ℂ)) 2 := by
  have hbound : ‖(1 / 4 : ℂ)‖ ≤
      (2 : ℝ) ^ (-(2 : ℝ) / 1) * |(2 : ℝ) - 1| ^ (((2 : ℝ) - 1) / 1) := by
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  obtain ⟨L, heq, hsum⟩ :=
    ramanujan_part1_ch3_entry14_lagrange_series 2 1 (by norm_num) (by norm_num)
      (by norm_num) (1 / 4) hbound
  have heq' : (1 / 4 : ℂ) * Complex.exp L ^ 2 - Complex.exp L + 1 = 0 := by
    norm_num at heq
    rw [show (2 : ℂ) * L = L + L by ring, Complex.exp_add] at heq
    rw [pow_two]
    exact heq
  have hsquare : (Complex.exp L - 2) ^ 2 = 0 := by
    calc
      (Complex.exp L - 2) ^ 2 = 4 *
          ((1 / 4 : ℂ) * Complex.exp L ^ 2 - Complex.exp L + 1) := by ring
      _ = 0 := by rw [heq', mul_zero]
  have hL : Complex.exp L = 2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  refine ⟨L, hL, ?_⟩
  simpa [hL] using hsum 1

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Entry14LagrangeSeries
