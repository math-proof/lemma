import Def.Data.Holor.BandPart
import Def.Data.Holor.Eye
import Instance.LinearAlgebra.Matrix.Matmul
import Mathlib.Data.Matrix.Basic


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


/--
`matProd f = f 0 * ⋯ * f (m - 1)`, and `matProd f = 1` when `m = 0`.
Factors indexed by `Fin m` (same shape as `Tensor.matProd`).
-/
def Matrix.matProd {n : ℕ} {α : Type*} [Semiring α] :
    (m : ℕ) → (Fin m → Matrix (Fin n) (Fin n) α) → Matrix (Fin n) (Fin n) α
  | 0, _ => 1
  | m + 1, f => (matProd m (fun i => f i.castSucc)) * (f (Fin.last m))


