import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.GeneralizedChebyshevSecondKind

open Polynomial
open MetaMathlibExt.GeneralizedChebyshevSecondKind

/--
[P_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma P_zero_eq
  [CommRing R]
-- given
  (r s : R) :
-- imply
  P r s 0 = 1 := by
-- proof
  apply P_zero


/--
[P_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma P_one_eq
  [CommRing R]
-- given
  (r s : R) :
-- imply
  P r s 1 = X - C r := by
-- proof
  apply P_one


/--
[P_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma P_succ_succ_eq
  [CommRing R]
-- given
  (r s : R) (n : ℕ) :
-- imply
  P r s (n + 2) = (X - C r) * P r s (n + 1) - C s * P r s n := by
-- proof
  apply P_succ_succ


/--
[Q_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma Q_zero_eq
  [CommRing R]
-- given
  (r s lam mu : R) :
-- imply
  Q r s lam mu 0 = 1 := by
-- proof
  apply Q_zero


/--
[Q_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma Q_one_eq
  [CommRing R]
-- given
  (r s lam mu : R) :
-- imply
  Q r s lam mu 1 = P r s 1 - C lam * P r s 0 := by
-- proof
  apply Q_one


/--
[Q_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma Q_add_two_eq
  [CommRing R]
-- given
  (r s lam mu : R) (n : ℕ) :
-- imply
  Q r s lam mu (n + 2) = P r s (n + 2) - C lam * P r s (n + 1) - C mu * P r s n := by
-- proof
  apply Q_add_two


/--
[Q_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean)
-/
@[path]
private lemma Q_recurrence_eq
  [CommRing R]
-- given
  (r s lam mu : R) (n : ℕ) :
-- imply
  Q r s lam mu (n + 3) = (X - C r) * Q r s lam mu (n + 2) - C s * Q r s lam mu (n + 1) := by
-- proof
  apply Q_recurrence


-- created on 2026-10-09
