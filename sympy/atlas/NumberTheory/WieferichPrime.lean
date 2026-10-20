/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# Wieferich primes to base two

A prime `p` is Wieferich to base two when `p ^ 2` divides `2 ^ (p - 1) - 1`.

## References

* Olivier Rozier, *Are the Collatz and abc conjectures related?*, arXiv:2306.15284v2
-/

namespace Nat

/-- A prime `p` is Wieferich to base two if `p ^ 2 ∣ 2 ^ (p - 1) - 1`. -/
def IsWieferichPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

instance decidableIsWieferichPrime (p : ℕ) : Decidable p.IsWieferichPrime := by
  unfold IsWieferichPrime
  infer_instance

/-- The divisibility and modular-congruence forms of the base-two Wieferich condition agree. -/
theorem isWieferichPrime_iff_modEq (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  rw [IsWieferichPrime, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (Nat.one_le_pow (p - 1) 2 (by decide))]

/-- The base-two Wieferich condition written using natural-number remainder. -/
theorem isWieferichPrime_iff_mod (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) % (p ^ 2) = 1 := by
  rw [isWieferichPrime_iff_modEq, Nat.ModEq]
  constructor
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩

end Nat
