import sympy.functions.special.tensor_functions
import sympy.tensor.stack

/--
Identity matrix of size `n x n` as a tensor that mimics the behavior of `torch.eye` or `sympy.Identity`.
- [sympy.Identity](https://github.com/sympy/sympy/blob/master/sympy/matrices/expressions/special.py#L104)
- [torch.eye](https://docs.pytorch.org/docs/stable/generated/torch.eye.html)
-/
def eye [AddMonoidWithOne α] [CharZero α] (n : Nat) : Tensor α [n, n] := [i < n] [j < n] (KroneckerDelta i j)
