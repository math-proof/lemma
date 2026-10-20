import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.AlfredFibonacciDeterminant
open MetaMathlibExt


/--
[alfred_consecutive_fibonacci_powers_determinant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/AlfredFibonacciDeterminant.lean)
-/
@[path]
private lemma alfred_consecutive_fibonacci_powers_determinant_eq
  {r : ℕ}
  {s k : ℤ} :
-- imply
  Matrix.det (fun (i j : Fin (r + 1)) =>
    Int.fib (s + (i.val : ℤ) * k) ^ (r - j.val) *
    Int.fib (s + ((i.val : ℤ) + 1) * k) ^ j.val) =
    (-1 : ℤ) ^ (((s + 1) * (Nat.choose (r + 1) 2 : ℤ) +
    k * (Nat.choose (r + 1) 3 : ℤ)).natAbs) *
    (Int.fib k ^ Nat.choose (r + 1) 2 *
    Finset.prod (Finset.Icc 1 r)
    (fun ℓ => Int.fib (k * (ℓ : ℤ)) ^ (r + 1 - ℓ))) := by
-- proof
  apply MetaMathlibExt.alfred_consecutive_fibonacci_powers_determinant r s k


-- created on 2026-10-20
