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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part9
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagBlockSwap_congr_right {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hbd : b < d) (hcd : c = d) :
    zagBlockSwap a b c hab hbc = zagBlockSwap a b d hab hbd := by
  subst d
  rfl

@[simp]
theorem zagBlockSwap_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc p : ℕ) = zagBlockSwapNat a b c p :=
  rfl

@[simp]
theorem zagBlockSwap_symm_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    ((zagBlockSwap a b c hab hbc).symm p : ℕ) =
      zagBlockUnswapNat a b c p :=
  rfl

end MetaMathlibExt
