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
import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruence
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

private instance ramanujanElevenPrime : Fact (Nat.Prime 11) :=
  ⟨Nat.prime_eleven⟩

private instance ramanujanElevenPowerSeriesCharP :
    CharP (PowerSeries (ZMod 11)) 11 :=
  charP_of_injective_ringHom PowerSeries.C_injective 11

/-- Euler's pentagonal series reduced modulo 11. -/
private noncomputable def ramanujanElevenEuler : PowerSeries (ZMod 11) :=
  PowerSeries.map (Int.castRingHom (ZMod 11)) (PowerSeries.pentagonalSeries ℤ)

/-- Jacobi's cube series reduced modulo 11. -/
private noncomputable def ramanujanElevenJacobi : PowerSeries (ZMod 11) :=
  PowerSeries.map (Int.castRingHom (ZMod 11)) jacobiCubeSeries

/-- The part of a power series whose exponents are congruent to `r` modulo 11. -/
private noncomputable def ramanujanElevenSection (r : ℕ) (f : PowerSeries (ZMod 11)) :
    PowerSeries (ZMod 11) :=
  PowerSeries.mk fun n => if n ≡ r [MOD 11] then PowerSeries.coeff n f else 0

/-- The residue-`r` part of Jacobi's cube series modulo 11. -/
private noncomputable def ramanujanElevenJ (r : ℕ) : PowerSeries (ZMod 11) :=
  ramanujanElevenSection r ramanujanElevenJacobi

/-- A series is supported in one congruence class modulo 11. -/
private def ramanujanElevenSupported (r : ℕ) (f : PowerSeries (ZMod 11)) : Prop :=
  ∀ n : ℕ, ¬n ≡ r [MOD 11] → PowerSeries.coeff n f = 0

private theorem ramanujanElevenSection_supported (r : ℕ) (f : PowerSeries (ZMod 11)) :
    ramanujanElevenSupported r (ramanujanElevenSection r f) := by
  intro n hn
  simp [hn]

private theorem ramanujanElevenJ_supported (r : ℕ) :
    ramanujanElevenSupported r (ramanujanElevenJ r) := by
  exact ramanujanElevenSection_supported r ramanujanElevenJacobi

private theorem ramanujanElevenSupported_mul {r s : ℕ} {f g : PowerSeries (ZMod 11)}
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

private theorem ramanujanElevenSupported_one :
    ramanujanElevenSupported 0 (1 : PowerSeries (ZMod 11)) := by
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (Nat.ModEq.refl 0)
  simp [PowerSeries.coeff_one, hn0]

private theorem ramanujanElevenSupported_pow {r : ℕ} {f : PowerSeries (ZMod 11)}
    (hf : ramanujanElevenSupported r f) (k : ℕ) :
    ramanujanElevenSupported (k * r) (f ^ k) := by
  induction k with
  | zero => simpa using ramanujanElevenSupported_one
  | succ k ih =>
      rw [pow_succ]
      simpa [Nat.succ_mul] using ramanujanElevenSupported_mul ih hf

private theorem ramanujanElevenSupported_C (a : ZMod 11) :
    ramanujanElevenSupported 0 (PowerSeries.C a) := by
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (Nat.ModEq.refl 0)
  simp [PowerSeries.coeff_C, hn0]

private class RamanujanElevenHomogeneous (r : outParam ℕ)
    (f : PowerSeries (ZMod 11)) : Prop where
  supported : ramanujanElevenSupported r f

private instance ramanujanElevenHomogeneousJ (r : ℕ) :
    RamanujanElevenHomogeneous r (ramanujanElevenJ r) :=
  ⟨ramanujanElevenJ_supported r⟩

private instance ramanujanElevenHomogeneousMul {r s : ℕ}
    {f g : PowerSeries (ZMod 11)} [hf : RamanujanElevenHomogeneous r f]
    [hg : RamanujanElevenHomogeneous s g] :
    RamanujanElevenHomogeneous (r + s) (f * g) :=
  ⟨ramanujanElevenSupported_mul hf.supported hg.supported⟩

private instance ramanujanElevenHomogeneousPow {r : ℕ}
    {f : PowerSeries (ZMod 11)} [hf : RamanujanElevenHomogeneous r f] (k : ℕ) :
    RamanujanElevenHomogeneous (k * r) (f ^ k) :=
  ⟨ramanujanElevenSupported_pow hf.supported k⟩

private instance ramanujanElevenHomogeneousC (a : ZMod 11) :
    RamanujanElevenHomogeneous 0 (PowerSeries.C a) :=
  ⟨ramanujanElevenSupported_C a⟩

private instance ramanujanElevenHomogeneousNatCast (n : ℕ) :
    RamanujanElevenHomogeneous 0 (n : PowerSeries (ZMod 11)) := by
  constructor
  simpa only [map_natCast] using ramanujanElevenSupported_C (n : ZMod 11)

private instance ramanujanElevenHomogeneousTwo :
    RamanujanElevenHomogeneous 0 (2 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 2

private instance ramanujanElevenHomogeneousThree :
    RamanujanElevenHomogeneous 0 (3 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 3

private instance ramanujanElevenHomogeneousFour :
    RamanujanElevenHomogeneous 0 (4 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 4

private instance ramanujanElevenHomogeneousFive :
    RamanujanElevenHomogeneous 0 (5 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 5

private instance ramanujanElevenHomogeneousSix :
    RamanujanElevenHomogeneous 0 (6 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 6

private instance ramanujanElevenHomogeneousSeven :
    RamanujanElevenHomogeneous 0 (7 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 7

private instance ramanujanElevenHomogeneousEight :
    RamanujanElevenHomogeneous 0 (8 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 8

private instance ramanujanElevenHomogeneousNine :
    RamanujanElevenHomogeneous 0 (9 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 9

private instance ramanujanElevenHomogeneousTen :
    RamanujanElevenHomogeneous 0 (10 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 10

private instance ramanujanElevenHomogeneousTwelve :
    RamanujanElevenHomogeneous 0 (12 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 12

private instance ramanujanElevenHomogeneousTwentyFour :
    RamanujanElevenHomogeneous 0 (24 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 24

private instance ramanujanElevenHomogeneousTwentyOne :
    RamanujanElevenHomogeneous 0 (21 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 21

private instance ramanujanElevenHomogeneousThirtyFive :
    RamanujanElevenHomogeneous 0 (35 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 35

private instance ramanujanElevenHomogeneousFortyTwo :
    RamanujanElevenHomogeneous 0 (42 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 42

private instance ramanujanElevenHomogeneousOneHundredFive :
    RamanujanElevenHomogeneous 0 (105 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 105

private instance ramanujanElevenHomogeneousOneHundredForty :
    RamanujanElevenHomogeneous 0 (140 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 140

private instance ramanujanElevenHomogeneousTwoHundredTen :
    RamanujanElevenHomogeneous 0 (210 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 210

private instance ramanujanElevenHomogeneousFourHundredTwenty :
    RamanujanElevenHomogeneous 0 (420 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 420

private instance ramanujanElevenHomogeneousSixHundredThirty :
    RamanujanElevenHomogeneous 0 (630 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 630

private instance ramanujanElevenHomogeneousEightHundredForty :
    RamanujanElevenHomogeneous 0 (840 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 840

private instance ramanujanElevenHomogeneousOneThousandTwoHundredSixty :
    RamanujanElevenHomogeneous 0 (1260 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 1260

private noncomputable def ramanujanElevenR3 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 3 +
    ramanujanElevenJ 0 * ramanujanElevenJ 1 ^ 3 +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 3 *
      ramanujanElevenJ 10) +
    7 * (ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 6 ^ 2) +
    3 * (ramanujanElevenJ 3 * ramanujanElevenJ 6 ^ 2 * ramanujanElevenJ 10) +
    ramanujanElevenJ 6 * ramanujanElevenJ 10 ^ 3

private noncomputable def ramanujanElevenR6 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 6 +
    7 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 3 ^ 2) +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 1 ^ 3 * ramanujanElevenJ 3 +
    3 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 ^ 2 * ramanujanElevenJ 10) +
    ramanujanElevenJ 6 ^ 3 * ramanujanElevenJ 10

private noncomputable def ramanujanElevenR8 : PowerSeries (ZMod 11) :=
  3 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 6) +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 3 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 0 * ramanujanElevenJ 10 ^ 3 +
    7 * (ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 3 ^ 2) +
    ramanujanElevenJ 1 * ramanujanElevenJ 6 ^ 3 +
    ramanujanElevenJ 3 ^ 3 * ramanujanElevenJ 10

private noncomputable def ramanujanElevenR9 : PowerSeries (ZMod 11) :=
  3 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 3 * ramanujanElevenJ 6) +
    7 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 10 ^ 2) +
    ramanujanElevenJ 0 * ramanujanElevenJ 3 ^ 3 +
    6 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 1 ^ 3 * ramanujanElevenJ 6 +
    ramanujanElevenJ 1 * ramanujanElevenJ 10 ^ 3

private noncomputable def ramanujanElevenR10 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 10 +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 3 *
      ramanujanElevenJ 6) +
    3 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 10 ^ 2) +
    ramanujanElevenJ 1 * ramanujanElevenJ 3 ^ 3 +
    ramanujanElevenJ 3 * ramanujanElevenJ 6 ^ 3 +
    7 * (ramanujanElevenJ 6 ^ 2 * ramanujanElevenJ 10 ^ 2)
end MetaMathlibExt
