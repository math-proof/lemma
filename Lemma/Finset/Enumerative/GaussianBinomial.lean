import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GaussianBinomial
open MathlibExt


/--
[gaussBinom_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_zero_right_eq
  [Semiring R]
  {Q : R}
  {M : ℕ} :
-- imply
  gaussBinom Q M 0 = 1 := by
-- proof
  apply MathlibExt.gaussBinom_zero_right Q M

/--
[gaussBinom_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_zero_succ_eq
  [Semiring R]
  {Q : R}
  {k : ℕ} :
-- imply
  gaussBinom Q 0 (k + 1) = 0 := by
-- proof
  apply MathlibExt.gaussBinom_zero_succ Q k

/--
[gaussBinom_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_succ_succ_eq
  [Semiring R]
  {Q : R}
  {M k : ℕ} :
-- imply
  gaussBinom Q (M + 1) (k + 1)
    = gaussBinom Q M k + Q ^ (k + 1) * gaussBinom Q M (k + 1) := by
-- proof
  apply MathlibExt.gaussBinom_succ_succ Q M k

/--
[gaussBinom_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_eq_zero_of_lt_eq
  [Semiring R]
  {Q : R}
  {M k : ℕ}
-- given
  (h : M < k) :
-- imply
  gaussBinom Q M k = 0 := by
-- proof
  apply MathlibExt.gaussBinom_eq_zero_of_lt Q M k h

/--
[gaussBinom_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_self_eq
  [Semiring R]
  {Q : R}
  {M : ℕ} :
-- imply
  gaussBinom Q M M = 1 := by
-- proof
  apply MathlibExt.gaussBinom_self Q M

/--
[qPochFin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma qPochFin_zero_eq
  [CommRing R]
  {Q : R} :
-- imply
  qPochFin Q 0 = 1 := by
-- proof
  apply MathlibExt.qPochFin_zero Q

/--
[qPochFin_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma qPochFin_succ_eq
  [CommRing R]
  {Q : R}
  {m : ℕ} :
-- imply
  qPochFin Q (m + 1) = qPochFin Q m * (1 - Q ^ (m + 1)) := by
-- proof
  apply MathlibExt.qPochFin_succ Q m

/--
[gaussBinom_mul_qPochFin_mul_qPochFin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
private lemma gaussBinom_mul_qPochFin_mul_qPochFin_eq
  [CommRing R]
  {Q : R}
  {M k : ℕ}
-- given
  (h : k ≤ M) :
-- imply
  gaussBinom Q M k * qPochFin Q k * qPochFin Q (M - k)
    = qPochFin Q M := by
-- proof
  apply MathlibExt.gaussBinom_mul_qPochFin_mul_qPochFin Q M k h


-- created on 2026-10-20
