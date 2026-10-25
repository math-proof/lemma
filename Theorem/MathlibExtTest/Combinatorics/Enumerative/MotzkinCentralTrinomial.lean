/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MotzkinCentralTrinomial.lean -/


import Lemma.Finset.Enumerative.MotzkinCentralTrinomial


namespace MetaMathlibExt

-- The binomial sum evaluates the first two nontrivial requested values.
example :
    trinomialCoefficient 4 4 = 19 ∧ trinomialCoefficient 5 5 = 51 := by
  constructor
  · rw [trinomialCoefficient_self_eq_sum]
    decide
  · rw [trinomialCoefficient_self_eq_sum]
    decide

-- The recurrence at `n = 3` uses the defining Motzkin sum `M 2 = 2`.
example : trinomialCoefficient 4 4 = trinomialCoefficient 3 3 + 12 := by
  let M : ℕ → ℕ := fun n =>
    ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k
  have hM : ∀ n, M n =
      ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k := by
    intro n
    rfl
  have hM2 : M 2 = 2 := by
    change (∑ k ∈ Finset.range (2 / 2 + 1),
      (2 : ℕ).choose (2 * k) * catalan k) = 2
    norm_num [Finset.sum_range_succ]
  have h := motzkin_central_trinomial_recurrence M hM 3 (by decide)
  rw [hM2] at h
  norm_num at h
  exact h

end MetaMathlibExt
