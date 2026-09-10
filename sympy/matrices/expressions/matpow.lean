import sympy.concrete.products
import sympy.matrices.dense
import sympy.tensor.stack
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


/--
[sympy.MatPow](https://github.com/sympy/sympy/blob/master/sympy/matrices/expressions/matpow.py)

matrix power `X ^ d` with integer exponent `d`:
- `d = 0`: `X ^ 0 = eye n`, unconditionally (mirrors Lean's `0 ^ 0 = 1`)
- `d > 0`: `X ^ d = X @ ⋯ @ X` (`d` factors)
- `d < 0`: `X ^ d = X.inv @ ⋯ @ X.inv` (`-d` factors)
-/
noncomputable def Tensor.MatPow [CommRing α] [CharZero α] (X : Tensor α [n, n]) (d : Int) : Tensor α [n, n] :=
  if d ≥ 0 then
    Tensor.matProd d.toNat (fun _ => X)
  else
    Tensor.matProd (-d).toNat (fun _ => X.inv)


noncomputable instance [CommRing α] [CharZero α] : HPow (Tensor α [m, m]) Int (Tensor α [m, m]) := ⟨Tensor.MatPow⟩
