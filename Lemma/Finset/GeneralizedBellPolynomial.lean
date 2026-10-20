import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.GeneralizedBellPolynomial
open scoped BigOperators
open MetaMathlibExt


/--
[genStirling_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
private lemma genStirling_zero_zero_eq
  [CommRing R]
  {s h : R} :
-- imply
  genStirling s h 0 0 = 1 := by
-- proof
  apply MetaMathlibExt.genStirling_zero_zero s h

/--
[genStirling_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
private lemma genStirling_zero_succ_eq
  [CommRing R]
  {s h : R}
  {k : ℕ} :
-- imply
  genStirling s h 0 (k + 1) = 0 := by
-- proof
  apply MetaMathlibExt.genStirling_zero_succ s h k

/--
[genStirling_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
private lemma genStirling_succ_zero_eq
  [CommRing R]
  {s h : R}
  {n : ℕ} :
-- imply
  genStirling s h (n + 1) 0 = 0 := by
-- proof
  apply MetaMathlibExt.genStirling_succ_zero s h n

/--
[genStirling_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
private lemma genStirling_succ_succ_eq
  [CommRing R]
  {s h : R}
  {n k : ℕ} :
-- imply
  genStirling s h (n + 1) (k + 1) = genStirling s h n k +
      h * ((↑(k + 1) : R) + s * (↑(n - (k + 1)) : R)) *
        genStirling s h n (k + 1) := by
-- proof
  apply MetaMathlibExt.genStirling_succ_succ s h n k

/--
[genBellPolynomial_eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
private lemma genBellPolynomial_eval_one_eq
  [CommRing R]
  {s h : R}
  {n : ℕ} :
-- imply
  genBellPolynomial s h n 1 = genBellNumber s h n := by
-- proof
  apply MetaMathlibExt.genBellPolynomial_eval_one s h n


-- created on 2026-10-20
