import sympy.matrices.dense
import torch.stack
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/--
matrix inverse: the adjugate divided by the determinant;
it is `0` when `det X` is not invertible.

Mirrors [sympy.Inverse](https://github.com/sympy/sympy/blob/master/sympy/matrices/inverse.py)
and Mathlib's `Matrix.inv`.
Note: `X⁻¹` remains the element-wise inverse (`Inv (Tensor α s)` instance);
use `X.inv` for the matrix inverse.
-/
noncomputable def Tensor.inv [CommRing α] (X : Tensor α [n, n]) : Tensor α [n, n] :=
  [i < n] [j < n] (X.toMatrix)⁻¹ i j
