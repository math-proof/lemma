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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part7
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagProduct_cycleCount_even {n : ℕ}
    (σ τ : Equiv.Perm (Fin n))
    (hσ : Multiset.card σ.cycleType +
      Fintype.card (Function.fixedPoints σ) = 1)
    (hτ : Multiset.card τ.cycleType +
      Fintype.card (Function.fixedPoints τ) = 1) :
    Even (n - (Multiset.card (σ * τ).cycleType +
      Fintype.card (Function.fixedPoints (σ * τ)))) := by
  have hs : σ.sign = (-1 : ℤˣ) ^ (n - 1) := by
    rw [zagSign_eq_neg_one_pow_cycleCount, hσ]
  have ht : τ.sign = (-1 : ℤˣ) ^ (n - 1) := by
    rw [zagSign_eq_neg_one_pow_cycleCount, hτ]
  have hp : (σ * τ).sign = 1 := by
    rw [Equiv.Perm.sign_mul, hs, ht, ← pow_add]
    exact (Even.add_self (n - 1)).neg_one_pow
  rw [zagSign_eq_neg_one_pow_cycleCount] at hp
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hp

theorem zagCard_cyclePairs_eq_zero_of_odd (n k : ℕ) (hodd : Odd (n - k)) :
    Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
      Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
      Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
      Multiset.card (p.1 * p.2).cycleType +
        Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun p => ?_⟩
  have heven := zagProduct_cycleCount_even p.1.1 p.1.2 p.2.1 p.2.2.1
  rw [p.2.2.2] at heven
  exact (Nat.not_even_iff_odd.mpr hodd heven).elim

end MetaMathlibExt
