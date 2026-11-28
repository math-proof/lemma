module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Instance.Data.Tensor.Tensor

@[expose] public section

open scoped Matrix


/--
Convert a rank-2 `Tensor` to a mathlib `Matrix` of scalar tensors.

Mirrors [sympy.Matrix](https://github.com/sympy/sympy/blob/master/sympy/matrices/dense.py#L144).
-/
def Tensor.toMatrix (X : Tensor α [m, n]) : Matrix (Fin m) (Fin n) (Tensor α []) :=
  fun i j => X[i.val, j.val]


