/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PowerFree.lean -/


import Def.NumberTheory.PowerFree
import Lemma.Nat.PowerFree
/-!
# Examples for power-free natural numbers
-/


namespace Nat

/-- `1` is power-free at level `2`. -/
example : Nat.IsPowerFree 1 2 :=
  isPowerFree_two.mpr squarefree_one

/-- Every prime is power-free at level `2`. -/
example {p : ℕ} (hp : p.Prime) : p.IsPowerFree 2 :=
  isPowerFree_two.mpr (Nat.prime_iff.mp hp).squarefree

/-- The squarefree bridge, forward direction. -/
example {n : ℕ} (h : n.IsPowerFree 2) : Squarefree n :=
  isPowerFree_two.mp h

/-- The squarefree bridge, reverse direction. -/
example {n : ℕ} (h : Squarefree n) : n.IsPowerFree 2 :=
  isPowerFree_two.mpr h

/-- The exponent restriction is sharp: nothing is `1`-free. -/
example (n : ℕ) : ¬n.IsPowerFree 1 :=
  fun h => absurd h.two_le (by decide)

/-- The positivity restriction is sharp: `0` is power-free at no level. -/
example (k : ℕ) : ¬Nat.IsPowerFree 0 k :=
  fun h => lt_irrefl 0 h.pos

/-- `8 = 2 ^ 3` is excluded at level `3` by the visible divisor `2 ^ 3`. -/
example : ¬Nat.IsPowerFree 8 3 := by
  intro h
  exact h.not_dvd Nat.prime_two (show (2 : ℕ) ^ 3 ∣ 8 by decide)

/-- `12` is excluded at level `2` by the visible divisor `2 ^ 2`. -/
example : ¬Nat.IsPowerFree 12 2 := by
  intro h
  exact h.not_dvd Nat.prime_two (show (2 : ℕ) ^ 2 ∣ 12 by decide)

/-- Divisors of a power-free number are power-free: any divisor of a prime
is `2`-free. -/
example {m p : ℕ} (hp : p.Prime) (hdiv : m ∣ p) : m.IsPowerFree 2 :=
  (isPowerFree_two.mpr (Nat.prime_iff.mp hp).squarefree).of_dvd hdiv

/-- A divisor of the concrete `2`-free prime `2` is `2`-free. -/
example : Nat.IsPowerFree 1 2 :=
  (isPowerFree_two.mpr (Nat.prime_iff.mp Nat.prime_two).squarefree).of_dvd (one_dvd 2)

/-- Monotonicity in the exponent: `2`-free implies `3`-free. -/
example {n : ℕ} (h : n.IsPowerFree 2) : n.IsPowerFree 3 :=
  h.mono (by decide)

/-- The concrete `2`-free prime `2` is `5`-free by monotonicity. -/
example : Nat.IsPowerFree 2 5 :=
  (isPowerFree_two.mpr (Nat.prime_iff.mp Nat.prime_two).squarefree).mono (by decide)

end Nat
