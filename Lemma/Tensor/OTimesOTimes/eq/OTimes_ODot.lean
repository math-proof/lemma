import sympy.concrete.prefix_sum.all_prefix_sums
import sympy.Basic


@[main]
private lemma main
  [OPlus α]
  [OTimes α]
  [ODot α]
  {a b c : α} :
-- imply
  ((a ⊗ b) ⊗ c) = a ⊗ (b ⊙ c) :=
  ODot.semiassociative a b c


-- created on 2024-12-08
