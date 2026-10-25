/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/MvPolynomial/PDeriv.lean -/


import Def.Algebra.MvPolynomial.PDeriv
import Lemma.MvPolynomial.PDeriv
open MvPolynomial


-- Mixed partial derivatives commute on a polynomial involving both variables.
example :
    pderiv 0 (pderiv 1 (X 0 * X 1 + C (2 : ℤ))) =
      pderiv 1 (pderiv 0 (X 0 * X 1 + C (2 : ℤ))) :=
  MvPolynomial.pderiv_comm 0 1 (X 0 * X 1 + C (2 : ℤ))

-- The empty mixed differential leaves a nonconstant polynomial fixed.
example :
    mixedDifferential []
        (X 0 + C (2 : ℤ)) = X 0 + C (2 : ℤ) :=
  mixedDifferential_nil _

-- A leading mixed differential can be peeled from a two-variable polynomial.
example :
    mixedDifferential [0, 1]
        (X 0 * X 1 + C (2 : ℤ)) =
      mixedDifferential [1]
        (X 0 * X 1 + C (2 : ℤ) - pderiv 0 (X 0 * X 1 + C (2 : ℤ))) :=
  mixedDifferential_cons 0 [1] _

-- Permuting two differentiation indices does not change the result.
example :
    mixedDifferential ([0, 1] : List (Fin 2))
        (X 0 * X 1 + C (2 : ℤ)) =
      mixedDifferential ([1, 0] : List (Fin 2))
        (X 0 * X 1 + C (2 : ℤ)) := by
  have hperm : ([0, 1] : List (Fin 2)).Perm [1, 0] :=
    (List.Perm.swap (0 : Fin 2) (1 : Fin 2) []).symm
  exact mixedDifferential_eq_of_perm hperm _

-- Appending two nonempty index lists composes their mixed differentials.
example :
    mixedDifferential ([0] ++ [1])
        (X 0 * X 1 + C (2 : ℤ)) =
      mixedDifferential [1]
        (mixedDifferential [0]
          (X 0 * X 1 + C (2 : ℤ))) :=
  mixedDifferential_append [0] [1] _

-- An additional partial derivative commutes with a nonempty mixed differential.
example :
    pderiv 0
        (mixedDifferential [1]
          (X 0 * X 1 + C (2 : ℤ))) =
      mixedDifferential [1]
        (pderiv 0 (X 0 * X 1 + C (2 : ℤ))) :=
  pderiv_mixedDifferential 0 [1] _

