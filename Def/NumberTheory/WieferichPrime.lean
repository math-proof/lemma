/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WieferichPrime.lean -/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

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

end Nat
