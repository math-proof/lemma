/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PascalTheorem.lean -/

import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs


namespace MetaMathlibExt

/-- Explicit 2D determinant used to turn collinearity into polynomial equations. -/
def D2 {k : Type*} [CommRing k] (x y : Fin 2 → k) : k := x 0 * y 1 - x 1 * y 0

end MetaMathlibExt
