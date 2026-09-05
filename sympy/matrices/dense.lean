import Mathlib.LinearAlgebra.Matrix.Defs
import sympy.tensor.tensor


/--
Convert a rank-2 `Tensor` to a mathlib `Matrix` of scalar tensors.

Mirrors [sympy.Matrix](https://github.com/sympy/sympy/blob/master/sympy/matrices/dense.py#L144).
-/
def Tensor.toMatrix (X : Tensor α [m, n]) : Matrix (Fin m) (Fin n) (Tensor α []) :=
  fun i j => X[i, j]
