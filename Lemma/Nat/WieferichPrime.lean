import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.NumberTheory.WieferichPrime
open Nat


namespace Nat

/--
[isWieferichPrime_iff_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean)
-/
@[path]
lemma isWieferichPrime_iff_modEq
  {p : ℕ} :
-- imply
  p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
-- proof
  rw [IsWieferichPrime, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (Nat.one_le_pow (p - 1) 2 (by decide))]

end Nat

namespace Nat

/--
[isWieferichPrime_iff_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean)
-/
@[path]
lemma isWieferichPrime_iff_mod
  {p : ℕ} :
-- imply
  p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) % (p ^ 2) = 1 := by
-- proof
  rw [isWieferichPrime_iff_modEq, Nat.ModEq]
  constructor
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
