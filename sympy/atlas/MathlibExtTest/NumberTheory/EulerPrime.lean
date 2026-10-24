/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EulerPrime.lean -/


import sympy.atlas.NumberTheory.EulerPrime
import Lemma.Nat.EulerPrime

open MetaMathlibExt

-- Boundary: the even perfect number 6 admits no Eulerian witness,
-- since the form requires oddness.
example : ∀ q k n, ¬ EulerianForm 6 q k n := by
  intro q k n h
  have hodd : Odd (6 : ℕ) := EulerianForm_odd h
  have hne : ¬ Odd (6 : ℕ) := by decide
  exact hne hodd

-- Boundary: hence 6 has no Euler prime at all.
example : ∀ q, ¬ IsEulerPrime 6 q := by
  intro q h
  have hodd : Odd (6 : ℕ) := IsEulerPrime_odd h
  have hne : ¬ Odd (6 : ℕ) := by decide
  exact hne hodd

-- Boundary: a composite proposed Euler prime 9 is rejected.
example : ∀ N k n, ¬ EulerianForm N 9 k n := by
  intro N k n h
  have hp : Nat.Prime (9 : ℕ) := EulerianForm_prime h
  have hne : ¬ Nat.Prime (9 : ℕ) := by decide
  exact hne hp

-- Boundary: hence 9 is the Euler prime of no number.
example : ∀ N, ¬ IsEulerPrime N 9 := by
  intro N h
  have hp : Nat.Prime (9 : ℕ) := IsEulerPrime_prime h
  have hne : ¬ Nat.Prime (9 : ℕ) := by decide
  exact hne hp

-- Hypothetical witness: projections recover primality, perfectness, oddness.
example (N q : ℕ) (h : IsEulerPrime N q) : Nat.Prime q :=
  IsEulerPrime_prime h

example (N q : ℕ) (h : IsEulerPrime N q) : Nat.Perfect N :=
  IsEulerPrime_perfect h

example (N q : ℕ) (h : IsEulerPrime N q) : Odd N :=
  IsEulerPrime_odd h

-- Hypothetical witness: the factorization must exist with all side conditions.
example (N q : ℕ) (h : IsEulerPrime N q) : ∃ k n, N = q ^ k * n ^ 2 :=
  IsEulerPrime_factor_eq h

example (N q : ℕ) (h : IsEulerPrime N q) :
    ∃ k n, N = q ^ k * n ^ 2 ∧ q % 4 = 1 ∧ k % 4 = 1 ∧
      Nat.Coprime q n :=
  IsEulerPrime_exists_factor h

-- Euler form: exact statement of the promoted theorem.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    ∃ q s m : ℕ,
      q.Prime ∧ n = q ^ s * m ^ 2 ∧ Nat.ModEq 4 q 1 ∧
        Nat.ModEq 4 s 1 ∧ q.Coprime m :=
  euler_odd_perfect_form n hodd hperf

-- Euler form: every odd perfect number has an Euler prime.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) : ∃ q, IsEulerPrime n q := by
  obtain ⟨q, s, m, hq, heq, hqmod, hsmod, hcop⟩ :=
    euler_odd_perfect_form n hodd hperf
  have hq4 : q % 4 = 1 := by
    have h := hqmod
    unfold Nat.ModEq at h
    omega
  have hs4 : s % 4 = 1 := by
    have h := hsmod
    unfold Nat.ModEq at h
    omega
  exact ⟨q, s, m, hperf, hodd, hq, heq, hq4, hs4, hcop⟩

-- Euler form: the Euler prime of a hypothetical odd perfect number is prime
-- and the full factorization with side conditions is available.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    ∃ q s m, q.Prime ∧ n = q ^ s * m ^ 2 ∧ q % 4 = 1 ∧ s % 4 = 1 ∧
      Nat.Coprime q m := by
  obtain ⟨q, s, m, hq, heq, hqmod, hsmod, hcop⟩ :=
    euler_odd_perfect_form n hodd hperf
  have hq4 : q % 4 = 1 := by
    have h := hqmod
    unfold Nat.ModEq at h
    omega
  have hs4 : s % 4 = 1 := by
    have h := hsmod
    unfold Nat.ModEq at h
    omega
  exact ⟨q, s, m, hq, heq, hq4, hs4, hcop⟩
