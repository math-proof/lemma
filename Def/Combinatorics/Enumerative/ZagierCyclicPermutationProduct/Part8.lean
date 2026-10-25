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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part7
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

def zagBlockSwapNat (a b c p : ℕ) : ℕ :=
  if p ≤ a then p
  else if p ≤ a + (c - b) then p + (b - a)
  else if p ≤ c then p - (c - b)
  else p

def zagBlockUnswapNat (a b c p : ℕ) : ℕ :=
  if p ≤ a then p
  else if p ≤ b then p + (c - b)
  else if p ≤ c then p - (b - a)
  else p

end MetaMathlibExt
