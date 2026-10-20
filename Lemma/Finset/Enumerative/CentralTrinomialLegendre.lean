import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CentralTrinomialLegendre
open MetaMathlibExt


/--
[centralTrinomialCoeff_eq_legendre_specialValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralTrinomialLegendre.lean)
-/
@[path]
private lemma centralTrinomialCoeff_eq_legendre_specialValue_eq
  {n : ℕ} :
-- imply
  (trinomialCoefficient n n : ℂ) =
    Complex.I ^ n * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) *
    Polynomial.aeval ((1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2)
    (Polynomial.shiftedLegendre n) := by
-- proof
  apply MetaMathlibExt.centralTrinomialCoeff_eq_legendre_specialValue n


-- created on 2026-10-20
