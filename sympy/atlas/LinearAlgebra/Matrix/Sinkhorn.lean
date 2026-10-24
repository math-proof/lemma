/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Sinkhorn.lean -/

import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.SinkhornWanted

private noncomputable def sinkJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (∑ j, A i j * Real.exp (u j)) - ∑ j, u j
end MathlibExt.LinearAlgebra.Matrix.SinkhornWanted
