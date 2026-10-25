/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean -/


import Lemma.Nat.Bernoulli.PolyBernoulliSymmetricExponentialGeneratingFunction


namespace MetaMathlibExt

-- At the origin, the symmetric generating function has value one.
example (B : ℕ → ℕ → ℝ)
    (hB : ∀ n k : ℕ,
      B n k = ∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * Nat.stirlingSecond (n + 1) (j + 1) *
          Nat.stirlingSecond (k + 1) (j + 1)) :
    (∑' n : ℕ, ∑' k : ℕ,
      B n k * ((0 : ℝ) ^ n / n.factorial) * ((0 : ℝ) ^ k / k.factorial)) = 1 := by
  simpa using
    polyBernoulli_negative_symmetric_exponential_generating_function B hB 0 0 (by norm_num)

end MetaMathlibExt
