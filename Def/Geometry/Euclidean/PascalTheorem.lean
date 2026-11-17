/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PascalTheorem.lean -/

module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace MetaMathlibExt

/-- Explicit 2D determinant used to turn collinearity into polynomial equations. -/
def D2 {k : Type*} [CommRing k] (x y : Fin 2 → k) : k := x 0 * y 1 - x 1 * y 0

end MetaMathlibExt
