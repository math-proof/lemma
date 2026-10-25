/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/


import Structure.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Theorem.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial


namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

noncomputable def monicChebyshev (n : ℕ) : Polynomial ℝ :=
  Polynomial.Chebyshev.T ℝ n *
    Polynomial.C (Polynomial.leadingCoeff (Polynomial.Chebyshev.T ℝ n))⁻¹

end MetaMathlibExt
