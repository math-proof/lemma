/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Section8Example4BernoulliIntegral.lean -/


import Lemma.Nat.Ramanujan.Part1Ch3Section8Example4BernoulliIntegral
import Mathlib.Tactic.NormNum

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 4 API checks

Values of `bernoulli`, and the theorem at `m = 0`, where it says `F(0, 1, x; 0) = x`.
-/

namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Section8Example4BernoulliIntegral

open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example4BernoulliIntegral
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

example : bernoulli 0 = 1 ∧ bernoulli 1 = -1 / 2 := ⟨bernoulli_zero, bernoulli_one⟩

example : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_two]

example (x : ℂ) : generalizedBellGenerating 0 1 x 0 = x := by
  simpa using (ramanujan_part1_ch3_section8_example4_bernoulli_integral 0 x).symm

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Section8Example4BernoulliIntegral
