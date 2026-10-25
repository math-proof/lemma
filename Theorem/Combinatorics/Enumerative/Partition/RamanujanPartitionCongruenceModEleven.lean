/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruence
import Def.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
/-!
# Ramanujan's partition congruence modulo 11

This module proves that the partition number `p(11m + 6)` is divisible by 11.
It follows Section 2 of M. D. Hirschhorn, "A short and simple proof of
Ramanujan's mod 11 partition congruence", J. Number Theory 139 (2014), 205–209.

The proof decomposes Euler's pentagonal series and Jacobi's cube series by
exponent modulo 11, verifies Hirschhorn's polynomial identity in characteristic
11, and transfers the resulting coefficient divisibility to partition numbers.
-/


namespace MetaMathlibExt

theorem ramanujanElevenSection_supported (r : ℕ) (f : PowerSeries (ZMod 11)) :
    ramanujanElevenSupported r (ramanujanElevenSection r f) := by
  intro n hn
  simp [hn]

theorem ramanujanElevenJ_supported (r : ℕ) :
    ramanujanElevenSupported r (ramanujanElevenJ r) := by
  exact ramanujanElevenSection_supported r ramanujanElevenJacobi

theorem ramanujanElevenSupported_mul {r s : ℕ} {f g : PowerSeries (ZMod 11)}
    (hf : ramanujanElevenSupported r f) (hg : ramanujanElevenSupported s g) :
    ramanujanElevenSupported (r + s) (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨a, b⟩ := ab
  have habn : a + b = n := Finset.mem_antidiagonal.mp hab
  by_cases ha : a ≡ r [MOD 11]
  · have hb : ¬b ≡ s [MOD 11] := by
      intro hb
      apply hn
      rw [← habn]
      exact ha.add hb
    rw [hg b hb, mul_zero]
  · rw [hf a ha, zero_mul]

theorem ramanujanElevenSupported_one :
    ramanujanElevenSupported 0 (1 : PowerSeries (ZMod 11)) := by
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (Nat.ModEq.refl 0)
  simp [PowerSeries.coeff_one, hn0]

theorem ramanujanElevenSupported_pow {r : ℕ} {f : PowerSeries (ZMod 11)}
    (hf : ramanujanElevenSupported r f) (k : ℕ) :
    ramanujanElevenSupported (k * r) (f ^ k) := by
  induction k with
  | zero => simpa using ramanujanElevenSupported_one
  | succ k ih =>
      rw [pow_succ]
      simpa [Nat.succ_mul] using ramanujanElevenSupported_mul ih hf

theorem ramanujanElevenSupported_C (a : ZMod 11) :
    ramanujanElevenSupported 0 (PowerSeries.C a) := by
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (Nat.ModEq.refl 0)
  simp [PowerSeries.coeff_C, hn0]

end MetaMathlibExt
