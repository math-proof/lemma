/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/UnitaryDivisorTests.lean -/


import sympy.atlas.NumberTheory.UnitaryDivisor
import Lemma.Set.UnitaryDivisor


example : Nat.unitaryDivisors 12 = {1, 3, 4, 12} := by decide

example : Nat.sigmaStar 12 = 20 := by decide

example {n d : ℕ} :
    d ∈ Nat.unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  rw [Nat.mem_unitaryDivisors]

example : Nat.unitaryDivisors 0 = ∅ := by simp

example : Nat.sigmaStar 0 = 0 := by simp

example {n d : ℕ} (h : d ∈ Nat.unitaryDivisors n) : d ∣ n :=
  Nat.dvd_of_mem_unitaryDivisors h

example {n d : ℕ} (h : d ∈ Nat.unitaryDivisors n) : d.Coprime (n / d) :=
  Nat.coprime_div_of_mem_unitaryDivisors h

example : ¬ (∅ : Set ℕ).IsPrimitiveByDivisibility 1 := by
  simp

example {S : Set ℕ} {n d : ℕ} (h : S.IsPrimitiveByDivisibility n)
    (hdvd : d ∣ n) (hdn : d < n) : d ∉ S :=
  h.not_mem_of_dvd_lt hdvd hdn
