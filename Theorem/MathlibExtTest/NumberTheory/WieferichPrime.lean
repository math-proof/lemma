/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/WieferichPrime.lean -/
module

public import Instance.NumberTheory.WieferichPrime
public import Theorem.Nat.WieferichPrime
public import Mathlib.Tactic.NormNum

public section

example : ¬Nat.IsWieferichPrime 2 := by
  norm_num [Nat.IsWieferichPrime]

example : ¬Nat.IsWieferichPrime 3 := by
  norm_num [Nat.IsWieferichPrime]

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 100000 in
example : Nat.IsWieferichPrime 1093 := by
  decide

example (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  Nat.isWieferichPrime_iff_modEq p

example (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) % (p ^ 2) = 1 :=
  Nat.isWieferichPrime_iff_mod p

