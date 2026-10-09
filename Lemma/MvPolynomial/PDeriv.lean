import Mathlib
import sympy.Basic
import sympy.Algebra.MvPolynomial.PDeriv

open MvPolynomial

/--
[pderiv_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma pderiv_comm_eq
  [CommSemiring k]
-- given
  (i j : σ) (p : MvPolynomial σ k) :
-- imply
  pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
-- proof
  apply pderiv_comm


/--
[mixedDifferential_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma mixedDifferential_nil_eq
  [CommRing k]
-- given
  (p : MvPolynomial σ k) :
-- imply
  mixedDifferential [] p = p := by
-- proof
  apply mixedDifferential_nil


/--
[mixedDifferential_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma mixedDifferential_cons_eq
  [CommRing k]
-- given
  (i : σ) (iis : List σ) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential (i :: iis) p = mixedDifferential iis (p - pderiv i p) := by
-- proof
  apply mixedDifferential_cons


/--
[mixedDifferential_eq_of_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma mixedDifferential_eq_of_perm_eq
  [CommRing k]
-- given
  {iis js : List σ} (h : iis.Perm js) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential iis p = mixedDifferential js p := by
-- proof
  apply mixedDifferential_eq_of_perm
  exact h


/--
[mixedDifferential_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma mixedDifferential_append_eq
  [CommRing k]
-- given
  (iis js : List σ) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential (iis ++ js) p = mixedDifferential js (mixedDifferential iis p) := by
-- proof
  apply mixedDifferential_append


/--
[pderiv_mixedDifferential](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
private lemma pderiv_mixedDifferential_eq
  [CommRing k]
-- given
  (i : σ) (iis : List σ) (p : MvPolynomial σ k) :
-- imply
  pderiv i (mixedDifferential iis p) = mixedDifferential iis (pderiv i p) := by
-- proof
  apply pderiv_mixedDifferential


-- created on 2026-10-09
