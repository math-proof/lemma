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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part43
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCyclePairs_recurrence
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1 - k) * Nat.card (ZagCyclePairs n k) =
      (∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagCyclePairs n (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by
  have h := zagPlaneConfig_recurrence n k hn hk hkn hparity
  have hcard (j : ℕ) :
      Nat.card (ZagPlaneConfig n hn j) = Nat.card (ZagCyclePairs n j) :=
    Nat.card_congr (zagPlaneConfigEquivCyclePairs n j hn)
  simp_rw [hcard] at h
  exact h

end MetaMathlibExt
