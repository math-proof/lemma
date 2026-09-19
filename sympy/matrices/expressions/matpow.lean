import sympy.concrete.products
import torch.stack
import torch.linalg.inv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


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
