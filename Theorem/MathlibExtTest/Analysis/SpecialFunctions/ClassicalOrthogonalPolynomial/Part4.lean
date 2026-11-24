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
public import Def.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/
namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

example : (chebyshevFamily.P 4).Monic := chebyshevFamily.monic 4

example : (chebyshevFamily.P 4).natDegree = 4 := chebyshevFamily.natDegree_eq 4

example : chebyshevFamily.weight 0 = 1 := by
  norm_num [chebyshevFamily, chebyshevWeight]

end MetaMathlibExt
