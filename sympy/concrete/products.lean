import sympy.matrices.expressions.special
import sympy.matrices.expressions.matmul


/--
`matProd f = f 0 @ ⋯ @ f (n - 1)`, and `matProd f = eye m` when `n = 0`.
Similar to `Stack`, the factors are indexed by `Fin n`.
-/
def Tensor.matProd
    [Mul α] [AddMonoidWithOne α] [CharZero α]
    {m : ℕ} :
    (n : ℕ) → (Fin n → Tensor α [m, m]) → Tensor α [m, m]
  | 0, _ => Tensor.eye m
  | n + 1, f => (matProd n (fun i => f i.castSucc)) @ (f (Fin.last n))
