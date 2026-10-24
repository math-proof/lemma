import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NoncentralTannyDowlingPolynomial
open MetaMathlibExt


variable (m a : ℤ)
/--
[w00](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w00 : noncentralWhitneySecond m a 0 0 = 1 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w01 : noncentralWhitneySecond m a 0 1 = 0 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w10](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w10 : noncentralWhitneySecond m a 1 0 = -a := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w11](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w11 : noncentralWhitneySecond m a 1 1 = 1 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w20](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w20 : noncentralWhitneySecond m a 2 0 = a ^ 2 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w21](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w21 : noncentralWhitneySecond m a 2 1 = -a + (m - a) := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w22](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w22 : noncentralWhitneySecond m a 2 2 = 1 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[w23](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma w23 : noncentralWhitneySecond m a 2 3 = 0 := by
  simp [noncentralWhitneySecond]

variable (m a : ℤ)
/--
[p0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma p0 : noncentralTannyDowlingPolynomial m a 0 = 1 := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond]

variable (m a : ℤ)
/--
[p1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma p1 :
  noncentralTannyDowlingPolynomial m a 1 = Polynomial.C (-a) + Polynomial.X := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond, Finset.sum_range_succ]

variable (m a : ℤ)
/--
[p2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NoncentralTannyDowlingPolynomial.lean)
-/
@[path]
private lemma p2 :
  noncentralTannyDowlingPolynomial m a 2 =
    Polynomial.C (a ^ 2) + Polynomial.C (-a + (m - a)) * Polynomial.X +
      2 * Polynomial.X ^ 2 := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond, Finset.sum_range_succ]


-- created on 2026-10-23
