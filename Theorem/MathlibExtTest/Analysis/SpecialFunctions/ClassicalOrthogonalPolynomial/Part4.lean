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
import Def.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial.Part3


namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

example : (chebyshevFamily.P 4).Monic := chebyshevFamily.monic 4

example : (chebyshevFamily.P 4).natDegree = 4 := chebyshevFamily.natDegree_eq 4

example : chebyshevFamily.weight 0 = 1 := by
  norm_num [chebyshevFamily, chebyshevWeight]

end MetaMathlibExt
