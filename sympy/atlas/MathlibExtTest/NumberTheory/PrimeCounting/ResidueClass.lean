/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/ResidueClass.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.ResidueClass
import Lemma.Nat.PrimeCounting.ResidueClass

-- `X = 0` has no primes.
example : Nat.primeCountingMod 0 3 1 = 0 := by decide

example : Nat.primeCountingMod 0 1 0 = 0 := by decide

-- Modulus one reduces to `Nat.primeCounting` and evaluates.
example : Nat.primeCountingMod 10 1 0 = 4 := by
  rw [Nat.primeCountingMod_one]
  decide

example : Nat.primeCountingMod 10 1 7 = 4 := by
  rw [Nat.primeCountingMod_one]
  decide

-- All three residue classes modulo 3 at `X = 10`.
-- Primes `≤ 10` are `{2,3,5,7}` with residues `2,0,2,1` mod 3.
example : Nat.primeCountingMod 10 3 2 = 2 := by decide

example : Nat.primeCountingMod 10 3 1 = 1 := by decide

example : Nat.primeCountingMod 10 3 0 = 1 := by decide

-- The endpoint is inclusive: the prime `11` is counted.
example : Nat.primeCountingMod 11 3 2 = 3 := by decide

-- Bridge lemma restates the count as a range filter.
example : Nat.primeCountingMod 10 3 2 =
    ((Finset.range (10 + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq 3 p 2).card :=
  Nat.primeCountingMod_eq_card_filter_range 10 3 2
