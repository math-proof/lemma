/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean -/

import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Rat

/-- Higher-order harmonic numbers: `H_n^(r) = ∑_{k=1}^n 1 / k ^ r` as rationals. -/
def higherHarmonic (n r : Nat) : Rat :=
  ∑ k ∈ Finset.Icc 1 n, (1 : Rat) / ((k : Rat) ^ r)

theorem higherHarmonic_zero (r : Nat) : higherHarmonic 0 r = 0 := by
  unfold higherHarmonic
  simp

theorem higherHarmonic_succ (n r : Nat) :
    higherHarmonic (n + 1) r =
      higherHarmonic n r + (1 : Rat) / ((((n + 1 : Nat)) : Rat) ^ r) := by
  unfold higherHarmonic
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

theorem higherHarmonic_one (r : Nat) : higherHarmonic 1 r = 1 := by
  unfold higherHarmonic
  rw [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_pow, div_one]

theorem higherHarmonic_order_one (n : Nat) : higherHarmonic n 1 = harmonic n := by
  induction n with
  | zero => simp [higherHarmonic, harmonic]
  | succ n ih =>
    rw [higherHarmonic_succ, ih, harmonic_succ, pow_one, one_div]
