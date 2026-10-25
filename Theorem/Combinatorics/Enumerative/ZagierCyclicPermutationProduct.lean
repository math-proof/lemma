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
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagMultiset_card_le_sum (m : Multiset ℕ)
    (hm : ∀ a ∈ m, 1 ≤ a) : m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      have ha : 1 ≤ a := hm a (by simp)
      have hm' : ∀ b ∈ m, 1 ≤ b := by
        intro b hb
        exact hm b (by simp [hb])
      simp only [Multiset.card_cons, Multiset.sum_cons]
      have := ih hm'
      omega

theorem zagCycleCount_even_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Even (n - (Multiset.card σ.cycleType +
      Fintype.card (Function.fixedPoints σ))) ↔
      Even (σ.cycleType.sum + Multiset.card σ.cycleType) := by
  rw [Equiv.Perm.card_fixedPoints]
  simp only [Fintype.card_fin]
  have hsum : σ.cycleType.sum ≤ n := by
    simpa using σ.sum_cycleType_le
  have hcard : Multiset.card σ.cycleType ≤ σ.cycleType.sum :=
    zagMultiset_card_le_sum σ.cycleType fun a ha =>
      (Equiv.Perm.two_le_of_mem_cycleType ha).trans' (by omega)
  have hsub :
      n - (Multiset.card σ.cycleType + (n - σ.cycleType.sum)) =
        σ.cycleType.sum - Multiset.card σ.cycleType := by
    omega
  rw [hsub]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r + Multiset.card σ.cycleType, ?_⟩
    omega
  · rintro ⟨r, hr⟩
    have hcr : Multiset.card σ.cycleType ≤ r := by omega
    refine ⟨r - Multiset.card σ.cycleType, ?_⟩
    omega

theorem zagSign_eq_neg_one_pow_cycleCount {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    σ.sign = (-1 : ℤˣ) ^
      (n - (Multiset.card σ.cycleType +
        Fintype.card (Function.fixedPoints σ))) := by
  rw [Equiv.Perm.sign_of_cycleType]
  exact neg_one_pow_congr (zagCycleCount_even_iff σ).symm

end MetaMathlibExt
