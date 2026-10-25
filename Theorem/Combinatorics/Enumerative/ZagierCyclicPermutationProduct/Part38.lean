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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part3
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCard_originalTotal_add_reflectedTotal
    (n k : ℕ) (hn : 0 < n) :
    Nat.card (ZagOriginalTotal n hn k 1) +
        Nat.card (ZagReflectedTotal n hn k) =
      (n - k) * Nat.card (ZagPlaneConfig n hn k) := by
  rw [Nat.card_sigma, Nat.card_sigma, ← Finset.sum_add_distrib]
  simp_rw [zagCard_original_add_reflected hn]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Nat.mul_comm]

end MetaMathlibExt
