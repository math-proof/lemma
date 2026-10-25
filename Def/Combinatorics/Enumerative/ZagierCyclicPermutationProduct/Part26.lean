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
import Inductive.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

def ZagOddMarks.depth {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {root : Fin n} : ZagOddMarks e π root → ℕ
  | .terminal _ => 0
  | .prepend _ _ _ _ _ _ _ tail => tail.depth + 1

def ZagOddMarks.toList {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {root : Fin n} : ZagOddMarks e π root → List (Fin n)
  | .terminal m => [m.first, m.middle, m.third]
  | .prepend first middle _ _ _ _ _ tail =>
      first :: middle :: tail.toList

end MetaMathlibExt
