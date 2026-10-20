import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.CatalanTransformPair
open scoped BigOperators
open MetaMathlibExt


/--
[catalan_transform_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/CatalanTransformPair.lean)
-/
@[path]
private lemma catalan_transform_pair_eq
  {a b : ℕ → ℚ}
-- given
  (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j) :
-- imply
  (∀ n, 0 < n → b n = ∑ k ∈ Finset.range (n + 1),
    ((k : ℚ) / (2 * (n : ℚ) - (k : ℚ))) * (Nat.choose (2 * n - k) (n - k) : ℚ) * a k) ∧
    (∀ n, 0 < n → b n = ∑ k ∈ Finset.range (n + 1),
    ((k : ℚ) / (n : ℚ)) * (Nat.choose (2 * n - k - 1) (n - k) : ℚ) * a k) ∧
    (∀ n, a n = ∑ k ∈ Finset.range (n / 2 + 1),
    (Nat.choose (n - k) k : ℚ) * (-1 : ℚ) ^ k * b (n - k)) ∧
    (∀ n, a n = ∑ k ∈ Finset.range (n + 1),
    (Nat.choose k (n - k) : ℚ) * (-1 : ℚ) ^ (n - k) * b k) := by
-- proof
  apply MetaMathlibExt.catalan_transform_pair a b h


-- created on 2026-10-20
