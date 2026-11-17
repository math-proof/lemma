/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/


module

public import Structure.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic
public import Theorem.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial

@[expose] public section

namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

noncomputable def monicChebyshev (n : ℕ) : Polynomial ℝ :=
  Polynomial.Chebyshev.T ℝ n *
    Polynomial.C (Polynomial.leadingCoeff (Polynomial.Chebyshev.T ℝ n))⁻¹

end MetaMathlibExt
