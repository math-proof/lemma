/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part37
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCycleQuotientCount_le {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : cycleQuotientCount σ ≤ n := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints]
  simp only [Fintype.card_fin]
  have hsum : σ.cycleType.sum ≤ n := by
    simpa using σ.sum_cycleType_le
  have hcard : Multiset.card σ.cycleType ≤ σ.cycleType.sum :=
    zagMultiset_card_le_sum σ.cycleType fun a ha =>
      (Equiv.Perm.two_le_of_mem_cycleType ha).trans' (by omega)
  omega

theorem zagVertical_cycleCount_odd {n k j : ℕ} (hn : 0 < n)
    (hparity : Even (n - k)) (e π : Equiv.Perm (Fin n))
    (hj : cycleQuotientCount π = j)
    (hdiag : cycleQuotientCount (zagDiagonal e π) = k) : Odd j := by
  let D := zagDiagonal e π
  let s := zagHorizontal e
  have hsignCount (σ : Equiv.Perm (Fin n)) :
      σ.sign = (-1 : ℤˣ) ^ (n - cycleQuotientCount σ) := by
    simpa only [cycleQuotientCount_eq] using zagSign_eq_neg_one_pow_cycleCount σ
  have hDsign : D.sign = 1 := by
    rw [hsignCount, show cycleQuotientCount D = k by exact hdiag]
    exact hparity.neg_one_pow
  have hfactor : D * π = s := by
    simp only [D, s, zagDiagonal]
    group
  have hsign : π.sign = s.sign := by
    have h := congrArg Equiv.Perm.sign hfactor
    rw [Equiv.Perm.sign_mul, hDsign, one_mul] at h
    exact h
  rw [hsignCount, hj] at hsign
  rw [hsignCount, show cycleQuotientCount s = 1 by
    exact zagHorizontal_cycleCount e hn] at hsign
  have hpowParity : Even (n - j) ↔ Even (n - 1) := by
    constructor
    · intro hjEven
      by_contra hsEven
      have hsOdd : Odd (n - 1) := Nat.not_even_iff_odd.mp hsEven
      have hone : (1 : ℤˣ) = -1 := by
        simpa only [hjEven.neg_one_pow, hsOdd.neg_one_pow] using hsign
      exact (by decide : (1 : ℤˣ) ≠ -1) hone
    · intro hsEven
      by_contra hjEven
      have hjOdd : Odd (n - j) := Nat.not_even_iff_odd.mp hjEven
      have hone : (-1 : ℤˣ) = 1 := by
        simpa only [hjOdd.neg_one_pow, hsEven.neg_one_pow] using hsign
      exact (by decide : (-1 : ℤˣ) ≠ 1) hone
  have hjle : j ≤ n := by
    rw [← hj]
    exact zagCycleQuotientCount_le π
  rw [Nat.even_sub' hjle, Nat.even_sub' (by omega : 1 ≤ n)] at hpowParity
  simp only [odd_one, iff_true] at hpowParity
  by_cases hnOdd : Odd n
  · exact (hpowParity.mpr hnOdd).mp hnOdd
  · by_contra hjOdd
    exact hnOdd (hpowParity.mp ⟨fun h => (hnOdd h).elim, fun h => (hjOdd h).elim⟩)

end MetaMathlibExt
