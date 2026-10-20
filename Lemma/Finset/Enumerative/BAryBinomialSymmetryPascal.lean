import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BAryBinomialSymmetryPascal
open MetaMathlibExt


/--
[bAryBinomialCoefficient_eq_prod_div_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialSymmetryPascal.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_eq_prod_div_pow_eq
  {b n k L : ℕ}
-- given
  (hb : 2 ≤ b)
  (hn : n < b ^ L)
  (hk : k < b ^ L) :
-- imply
  bAryBinomialCoefficient b n k hb =
    ∏ i ∈ Finset.range L, Nat.choose ((n / b ^ i) % b) ((k / b ^ i) % b) := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_eq_prod_div_pow b n k hb hn hk

/--
[bAryBinomialCoefficient_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialSymmetryPascal.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_symm_eq
  {b n k : ℕ}
-- given
  (hb : 2 ≤ b)
  (hkn : k ≤ n) :
-- imply
  bAryBinomialCoefficient b n k hb = bAryBinomialCoefficient b n (n - k) hb := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_symm b n k hb hkn

/--
[bAryBinomialCoefficient_pascal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialSymmetryPascal.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_pascal_eq
  {b n k : ℕ}
-- given
  (hb : 2 ≤ b)
  (hk : 0 < k)
  (hkn : k ≤ n)
  (hne : bAryBinomialCoefficient b n k hb ≠ 0) :
-- imply
  bAryBinomialCoefficient b n k hb =
    bAryBinomialCoefficient b (n - 1) (k - 1) hb + bAryBinomialCoefficient b (n - 1) k hb := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_pascal b n k hb hk hkn hne

/--
[baryBinomial_symmetry_and_pascal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialSymmetryPascal.lean)
-/
@[path]
private lemma baryBinomial_symmetry_and_pascal_eq
  {b : ℕ}
  {n k : ℤ}
-- given
  (hb : 2 ≤ b)
  (hn : 0 < n)
  (hk : 0 ≤ k)
  (hkn : k ≤ n) :
-- imply
  let baryBinomial : ℤ → ℤ → ℕ := by
-- proof
  apply MetaMathlibExt.baryBinomial_symmetry_and_pascal b hb n k hn hk hkn


-- created on 2026-10-20
