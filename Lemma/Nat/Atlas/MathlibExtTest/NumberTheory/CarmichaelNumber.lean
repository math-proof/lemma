import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.CarmichaelNumber


/--
[isCarmichaelNumber_561](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
private lemma isCarmichaelNumber_561 : Nat.IsCarmichaelNumber 561 := by
  have h561 : (1 : ℕ) < 561 := by norm_num
  rw [Nat.isCarmichaelNumber_iff_korselt 561 h561]
  refine ⟨?_, ?_, by norm_num⟩
  · have h : 561 = 3 * 11 * 17 := by norm_num
    rw [h]
    have h3 : Squarefree (3 : ℕ) :=
      Irreducible.squarefree (by norm_num : Nat.Prime 3)
    have h11 : Squarefree (11 : ℕ) :=
      Irreducible.squarefree (by norm_num : Nat.Prime 11)
    have h17 : Squarefree (17 : ℕ) :=
      Irreducible.squarefree (by norm_num : Nat.Prime 17)
    have hCop1 : Nat.Coprime 3 (11 * 17) := by norm_num
    have hCop2 : Nat.Coprime 11 17 := by norm_num
    have hSF11_17 : Squarefree (11 * 17) :=
      (Nat.squarefree_mul hCop2).mpr ⟨h11, h17⟩
    exact (Nat.squarefree_mul hCop1).mpr ⟨h3, hSF11_17⟩
  · intro p hp hpdvd
    have h561eq : 561 = 3 * 11 * 17 := by norm_num
    rw [h561eq] at hpdvd
    have h1 : p ∣ 3 * (11 * 17) := by rwa [mul_assoc] at hpdvd
    have h2 : p ∣ 3 ∨ p ∣ 11 * 17 := hp.dvd_mul.mp h1
    obtain h3 | h3 := h2
    · have hEq : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
      rw [hEq]
      norm_num
    · have h4 : p ∣ 11 ∨ p ∣ 17 := hp.dvd_mul.mp h3
      obtain h5 | h5 := h4
      · have hEq : p = 11 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).mp h5
        rw [hEq]
        norm_num
      · have hEq : p = 17 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp h5
        rw [hEq]
        norm_num


-- created on 2026-10-23
