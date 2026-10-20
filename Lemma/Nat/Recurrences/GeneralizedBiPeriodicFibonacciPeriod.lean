import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GeneralizedBiPeriodicFibonacciPeriod
open MetaMathlibExt


/--
[generalizedBiPeriodicFibonacci_period_dvd_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedBiPeriodicFibonacciPeriod.lean)
-/
@[path]
private lemma generalizedBiPeriodicFibonacci_period_dvd_general_eq
  :
-- imply
  ∀ (p : ℕ) (_hp : p.Prime) (_hpOdd : Odd p)
    (a b c d : ZMod p)
    (F : ℕ → ZMod p)
    (A Δ α β : ZMod p)
    (k : ℕ),
    F 0 = 0 →
    F 1 = 1 →
    (∀ n, 2 ≤ n → n % 2 = 0 →
    F n = a * F (n - 1) + c * F (n - 2)) →
    (∀ n, 2 ≤ n → n % 2 = 1 →
    F n = b * F (n - 1) + d * F (n - 2)) →
    a ≠ 0 →
    c ≠ 0 →
    d ≠ 0 →
    (a ≠ b ∨ c ≠ d) →
    A = a * b + c + d →
    Δ = A ^ 2 - 4 * c * d →
    α + β = A →
    α * β = c * d →
    0 < k →
    (∀ n, F (n + k) = F n) →
    (∀ m, 0 < m → (∀ n, F (n + m) = F n) → k ≤ m) →
    Δ ≠ 0 →
    k ∣ 2 * (p - 1) ∧
    ((α ≠ 0 ∧ IsSquare α ∧ β ≠ 0 ∧ IsSquare β) → k ∣ p - 1) := by
-- proof
  apply MetaMathlibExt.generalizedBiPeriodicFibonacci_period_dvd_general

/--
[generalizedBiPeriodicFibonacci_period_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedBiPeriodicFibonacciPeriod.lean)
-/
@[path]
private lemma generalizedBiPeriodicFibonacci_period_dvd_eq
  :
-- imply
  ∀ (p : ℕ) (hp : p.Prime) (hpOdd : Odd p)
    (a b c d : ZMod p)
    (F : ℕ → ZMod p)
    (A Δ α β : ZMod p)
    (k : ℕ),
    F 0 = 0 →
    F 1 = 1 →
    (∀ n, 2 ≤ n → n % 2 = 0 →
    F n = a * F (n - 1) + c * F (n - 2)) →
    (∀ n, 2 ≤ n → n % 2 = 1 →
    F n = b * F (n - 1) + d * F (n - 2)) →
    a ≠ 0 →
    c ≠ 0 →
    d ≠ 0 →
    (a ≠ b ∨ c ≠ d) →
    A = a * b + c + d →
    Δ = A ^ 2 - 4 * c * d →
    α + β = A →
    α * β = c * d →
    0 < k →
    (∀ n, F (n + k) = F n) →
    (∀ m, 0 < m → (∀ n, F (n + m) = F n) → k ≤ m) →
    Δ ≠ 0 →
    IsSquare Δ →
    k ∣ 2 * (p - 1) ∧
    ((α ≠ 0 ∧ IsSquare α ∧ β ≠ 0 ∧ IsSquare β) → k ∣ p - 1) := by
-- proof
  apply MetaMathlibExt.generalizedBiPeriodicFibonacci_period_dvd


-- created on 2026-10-20
