/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Bernoulli/PolyBernoulliDuality.lean -/


import sympy.atlas.NumberTheory.Bernoulli.PolyBernoulliDuality
import Lemma.Nat.Bernoulli.PolyBernoulliDuality
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- `B₀⁽ᵏ⁾ = 1` for every index.
example (k : ℤ) : polyBernoulli 0 k = 1 := by
  simp [polyBernoulli]

-- Positive indices: `B₁⁽¹⁾ = 1/2`, `B₂⁽¹⁾ = 1/6`, `B₂⁽²⁾ = -1/36`.
example : polyBernoulli 1 1 = 1 / 2 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

example : polyBernoulli 2 1 = 1 / 6 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

example : polyBernoulli 2 2 = -1 / 36 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

-- Negative indices: `B₁⁽⁻¹⁾ = 2`, `B₁⁽⁻²⁾ = 4`, `B₂⁽⁻¹⁾ = 4`, `B₂⁽⁻²⁾ = 14`.
example : polyBernoulli 1 (-1) = 2 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

example : polyBernoulli 1 (-2) = 4 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

example : polyBernoulli 2 (-1) = 4 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

example : polyBernoulli 2 (-2) = 14 := by
  norm_num [polyBernoulli, Finset.sum_range_succ, Nat.stirlingSecond]

-- Exercise the production theorem generically.
example (n k : ℕ) : polyBernoulli n (-(k : ℤ)) = polyBernoulli k (-(n : ℤ)) :=
  arakawa_kaneko_duality n k

-- Duality relates the two direct computations above.
example : polyBernoulli 1 (-2) = polyBernoulli 2 (-1) := by
  simpa using arakawa_kaneko_duality 1 2

#print axioms MetaMathlibExt.arakawa_kaneko_duality

end MetaMathlibExt
