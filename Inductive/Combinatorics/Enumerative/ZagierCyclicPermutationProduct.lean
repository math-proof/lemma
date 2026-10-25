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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part28
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

inductive ZagOddMarks {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Fin n → Type
  | terminal (m : ZagMarkedTriple e π) : ZagOddMarks e π m.first
  | prepend (first middle third : Fin n)
      (first_mem : first ∈ zagCycleMinima e π)
      (middle_mem : middle ∈ zagCycleMinima e π)
      (first_lt_middle : first < middle)
      (middle_lt_third : middle < third)
      (tail : ZagOddMarks e π third) : ZagOddMarks e π first

end MetaMathlibExt
