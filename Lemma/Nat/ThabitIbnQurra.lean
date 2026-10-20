import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ThabitIbnQurra
open scoped BigOperators
open MetaMathlibExt


/--
[thabit_ibn_qurra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThabitIbnQurra.lean)
-/
@[path]
private lemma thabit_ibn_qurra_eq
  :
-- imply
  ∀ (n p q r : ℕ), 2 ≤ n →
    p = 3 * 2 ^ n - 1 →
    q = 3 * 2 ^ (n - 1) - 1 →
    r = 9 * 2 ^ (2 * n - 1) - 1 →
    Nat.Prime p → Nat.Prime q → Nat.Prime r →
    2 ^ n * p * q < 2 ^ n * r ∧
    ∑ d ∈ Nat.properDivisors (2 ^ n * p * q), d = 2 ^ n * r ∧
    ∑ d ∈ Nat.properDivisors (2 ^ n * r), d = 2 ^ n * p * q := by
-- proof
  apply MetaMathlibExt.thabit_ibn_qurra


-- created on 2026-10-20
