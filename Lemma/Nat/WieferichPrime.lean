import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.WieferichPrime
open Nat


/--
[isWieferichPrime_iff_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean)
-/
@[path]
private lemma isWieferichPrime_iff_modEq_eq
  {p : ℕ} :
-- imply
  p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
-- proof
  apply Nat.isWieferichPrime_iff_modEq p

/--
[isWieferichPrime_iff_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean)
-/
@[path]
private lemma isWieferichPrime_iff_mod_eq
  {p : ℕ} :
-- imply
  p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) % (p ^ 2) = 1 := by
-- proof
  apply Nat.isWieferichPrime_iff_mod p


-- created on 2026-10-20
