import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.KlamkinBinomialReciprocal
open MetaMathlibExt


/--
[klamkin_binomial_reciprocal_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/KlamkinBinomialReciprocal.lean)
-/
@[path]
private lemma klamkin_binomial_reciprocal_identity_eq
  {n b x : ℕ}
-- given
  (h : n + b ≤ x) :
-- imply
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ) =
    ((x + 1 : ℕ) : ℚ) /
    (((x - n + 1 : ℕ) : ℚ) * (Nat.choose (x - n) b : ℚ)) := by
-- proof
  apply MetaMathlibExt.klamkin_binomial_reciprocal_identity n b x h


-- created on 2026-10-20
