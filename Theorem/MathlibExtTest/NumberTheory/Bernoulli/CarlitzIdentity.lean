/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Bernoulli/CarlitzIdentity.lean -/


import Def.NumberTheory.Bernoulli.CarlitzIdentity
import Lemma.Nat.Bernoulli.CarlitzIdentity


namespace MetaMathlibExt

example (m n : ℕ) :
    (-1 : ℚ) ^ m * (Finset.range (m + 1)).sum
      (fun k => (Nat.choose m k : ℚ) * bernoulli (n + k)) =
    (-1 : ℚ) ^ n * (Finset.range (n + 1)).sum
      (fun k => (Nat.choose n k : ℚ) * bernoulli (m + k)) :=
  carlitz_bernoulli_sum_symm m n

example :
    (-1 : ℚ) ^ (0 : ℕ) * (Finset.range (0 + 1)).sum
      (fun k => (Nat.choose 0 k : ℚ) * bernoulli (0 + k)) =
    (-1 : ℚ) ^ (0 : ℕ) * (Finset.range (0 + 1)).sum
      (fun k => (Nat.choose 0 k : ℚ) * bernoulli (0 + k)) :=
  carlitz_bernoulli_sum_symm 0 0

example :
    (-1 : ℚ) ^ (0 : ℕ) * (Finset.range (0 + 1)).sum
      (fun k => (Nat.choose 0 k : ℚ) * bernoulli (1 + k)) =
    (-1 : ℚ) ^ (1 : ℕ) * (Finset.range (1 + 1)).sum
      (fun k => (Nat.choose 1 k : ℚ) * bernoulli (0 + k)) :=
  carlitz_bernoulli_sum_symm 0 1

#print axioms MetaMathlibExt.carlitz_bernoulli_sum_symm

end MetaMathlibExt
