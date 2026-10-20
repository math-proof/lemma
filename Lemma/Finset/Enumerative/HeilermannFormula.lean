import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.HeilermannFormula
open scoped BigOperators
open MetaMathlibExt


/--
[hankelTransform_eq_prod_of_hasJacobiFraction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannFormula.lean)
-/
@[path]
private lemma hankelTransform_eq_prod_of_hasJacobiFraction_eq
  [CommRing K]
  {a alpha beta : ℕ → K}
  {mu0 : K}
  {F : ℕ → PowerSeries K}
  {n : ℕ}
-- given
  (h : HasJacobiFraction a alpha beta mu0 F) :
-- imply
  hankelTransform a n =
    mu0 ^ (n + 1) * ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
-- proof
  apply MetaMathlibExt.hankelTransform_eq_prod_of_hasJacobiFraction h n

/--
[hankelTransform_eq_of_hasJacobiFraction_same_beta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannFormula.lean)
-/
@[path]
private lemma hankelTransform_eq_of_hasJacobiFraction_same_beta_eq
  [CommRing K]
  {a a2 alpha alpha2 beta : ℕ → K}
  {mu0 : K}
  {F F2 : ℕ → PowerSeries K}
-- given
  (h0 : HasJacobiFraction a alpha beta mu0 F)
  (h1 : HasJacobiFraction a2 alpha2 beta mu0 F2) :
-- imply
  hankelTransform a = hankelTransform a2 := by
-- proof
  apply MetaMathlibExt.hankelTransform_eq_of_hasJacobiFraction_same_beta a a2 alpha alpha2 beta mu0 F F2 h0 h1


-- created on 2026-10-20
