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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part8
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagBlockSwapNat_lt {a b c p n : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < n) (hp : p < n) :
    zagBlockSwapNat a b c p < n := by
  simp only [zagBlockSwapNat]
  split_ifs <;> omega

theorem zagBlockUnswapNat_lt {a b c p n : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < n) (hp : p < n) :
    zagBlockUnswapNat a b c p < n := by
  simp only [zagBlockUnswapNat]
  split_ifs <;> omega

theorem zagBlockUnswapNat_swap {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockUnswapNat a b c (zagBlockSwapNat a b c p) = p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

theorem zagBlockSwapNat_unswap {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockSwapNat a b c (zagBlockUnswapNat a b c p) = p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

end MetaMathlibExt
