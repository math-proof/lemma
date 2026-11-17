/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Sinkhorn.lean -/

module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open Matrix


namespace MathlibExt.LinearAlgebra.Matrix.SinkhornWanted

noncomputable def sinkJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (∑ j, A i j * Real.exp (u j)) - ∑ j, u j

end MathlibExt.LinearAlgebra.Matrix.SinkhornWanted
