/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/

namespace Nat

/-- The unitary divisors of `n`: divisors coprime to their complementary divisors. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => d.Coprime (n / d)

@[simp]
theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

@[simp]
theorem unitaryDivisors_zero : unitaryDivisors 0 = ∅ := by
  simp [unitaryDivisors]

theorem dvd_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) : d ∣ n :=
  (mem_unitaryDivisors.mp h).1

theorem coprime_div_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) :
    d.Coprime (n / d) :=
  (mem_unitaryDivisors.mp h).2.2

/-- The sum of the unitary divisors of `n`, conventionally denoted `σ⋆(n)`. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

theorem sigmaStar_eq_sum (n : ℕ) :
    sigmaStar n = ∑ d ∈ unitaryDivisors n, d :=
  rfl

@[simp]
theorem sigmaStar_zero : sigmaStar 0 = 0 := by
  simp [sigmaStar]

end Nat

namespace Set

/-- A member `n` of `S ⊆ ℕ` is primitive under divisibility when no proper
divisor of `n` also belongs to `S`. -/
def IsPrimitiveByDivisibility (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

@[simp]
theorem isPrimitiveByDivisibility_iff {S : Set ℕ} {n : ℕ} :
    S.IsPrimitiveByDivisibility n ↔
      n ∈ S ∧ ∀ {d : ℕ}, d ∣ n → d < n → d ∉ S := by
  constructor
  · rintro ⟨hn, hdisjoint⟩
    refine ⟨hn, fun {d} hdvd hdlt hdS => ?_⟩
    exact Set.disjoint_left.mp hdisjoint (Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩) hdS
  · rintro ⟨hn, hminimal⟩
    refine ⟨hn, Set.disjoint_left.mpr ?_⟩
    intro d hdproper hdS
    exact hminimal (Nat.mem_properDivisors.mp hdproper).1
      (Nat.mem_properDivisors.mp hdproper).2 hdS

theorem IsPrimitiveByDivisibility.mem {S : Set ℕ} {n : ℕ}
    (h : S.IsPrimitiveByDivisibility n) : n ∈ S :=
  h.1

theorem IsPrimitiveByDivisibility.not_mem_of_dvd_lt {S : Set ℕ} {n d : ℕ}
    (h : S.IsPrimitiveByDivisibility n) (hdvd : d ∣ n) (hdn : d < n) : d ∉ S := by
  intro hd
  exact isPrimitiveByDivisibility_iff.mp h |>.2 hdvd hdn hd

end Set
