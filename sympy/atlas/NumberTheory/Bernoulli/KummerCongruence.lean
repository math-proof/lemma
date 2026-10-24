/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KummerCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.NumberTheory.PowModTotient
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Kummer's congruence

This file proves Kummer's congruence for the modified Bernoulli quotients using
Voronoi's finite-sum congruence and the p-adic norm on `ℚ`.
-/

namespace MetaMathlibExt

private def kummer_W (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, j ^ (k - 1) * (c * j / N)

private def kummer_U (p s c k : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range (p ^ s)).filter (fun j => ¬p ∣ j),
    j ^ (k - 1) * (c * j / p ^ s)

private def kummer_R (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, (c * j / N) * ((c * j) % N) ^ (k - 1)

private def kummer_H (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Icc 2 k,
    (N * (c * j / N)) ^ i * ((c * j) % N) ^ (k - i) * k.choose i

private def kummer_D (N c k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, ((c * j / N : ℕ) : ℤ) *
    ((((c * j) % N : ℕ) : ℤ) ^ (k - 1) - ((c * j : ℕ) : ℤ) ^ (k - 1))

private def kummer_padicBound (p : ℕ) (e : ℤ) (q : ℚ) : Prop :=
  padicNorm p q ≤ (p : ℚ) ^ (-e)

private noncomputable def kummer_E (N k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    bernoulli i * (Nat.choose (k + 1) i : ℚ) * (N : ℚ) ^ (k - i) / ((k : ℚ) + 1)

private noncomputable def kummer_beta (p k : ℕ) : ℚ :=
  (1 - (p : ℚ) ^ (k - 1)) * bernoulli k / k
end MetaMathlibExt
