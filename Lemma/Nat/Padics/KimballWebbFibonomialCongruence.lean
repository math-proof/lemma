import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.KimballWebbFibonomialCongruence
open MetaMathlibExt


/--
[fibonomial_prime_cube_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/KimballWebbFibonomialCongruence.lean)
-/
@[path]
private lemma fibonomial_prime_cube_congr_eq
  :
-- imply
  ∀ (p rho : ℕ) (ε : ℤ) (k : ℕ), Nat.Prime p → 7 ≤ p →
    (ε = 1 ∨ ε = -1) → (rho : ℤ) = (p : ℤ) - ε → Nat.fib rho % p = 0 →
    (∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) →
    Int.ModEq ((p : ℤ) ^ 3)
    (((Finset.prod (Finset.range ((k + 1) * rho - 1)) (fun i => Nat.fib (i + 1)) /
    (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) *
    Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1)))) : ℕ) : ℤ)
    (ε ^ k) := by
-- proof
  apply MetaMathlibExt.fibonomial_prime_cube_congr


-- created on 2026-10-20
