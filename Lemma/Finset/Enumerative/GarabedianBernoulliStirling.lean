import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GarabedianBernoulliStirling
open scoped BigOperators
open MetaMathlibExt


/--
[garabedian_genocchi_formula_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianBernoulliStirling.lean)
-/
@[path]
private lemma garabedian_genocchi_formula_general_eq
  {n : ℕ} :
-- imply
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n =
    n * ∑ k ∈ Finset.Icc 1 n,
    ((-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) *
    Nat.stirlingSecond n k) / (2 : ℚ) ^ (k - 1) := by
-- proof
  apply MetaMathlibExt.garabedian_genocchi_formula_general n

/--
[garabedian_genocchi_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianBernoulliStirling.lean)
-/
@[path]
private lemma garabedian_genocchi_formula_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n =
    n * ∑ k ∈ Finset.Icc 1 n,
    ((-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) *
    Nat.stirlingSecond n k) / (2 : ℚ) ^ (k - 1) := by
-- proof
  apply MetaMathlibExt.garabedian_genocchi_formula n hn


-- created on 2026-10-20
