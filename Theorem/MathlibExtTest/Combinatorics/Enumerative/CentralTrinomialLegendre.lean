/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CentralTrinomialLegendre.lean -/


import Def.Combinatorics.Enumerative.CentralTrinomialLegendre
import Lemma.Finset.Enumerative.CentralTrinomialLegendre


namespace MetaMathlibExt

-- The identity applies at every natural index.
example (n : ℕ) :
    (trinomialCoefficient n n : ℂ) =
      Complex.I ^ n * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) *
        Polynomial.aeval ((1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2)
          (Polynomial.shiftedLegendre n) :=
  centralTrinomialCoeff_eq_legendre_specialValue n

-- The identity specializes directly to index two.
example :
    (trinomialCoefficient 2 2 : ℂ) =
      Complex.I ^ 2 * (Real.sqrt ((3 : ℝ) ^ 2) : ℂ) *
        Polynomial.aeval ((1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2)
          (Polynomial.shiftedLegendre 2) :=
  centralTrinomialCoeff_eq_legendre_specialValue 2

end MetaMathlibExt
