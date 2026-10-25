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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part4
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem ZagMarkedTriple.toFinset_card {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
    m.toFinset.card = 3 := by
  have hfm : m.first ≠ m.middle := ne_of_lt m.first_lt_middle
  have hmt : m.middle ≠ m.third := ne_of_lt m.middle_lt_third
  have hft : m.first ≠ m.third :=
    ne_of_lt (m.first_lt_middle.trans m.middle_lt_third)
  simp [ZagMarkedTriple.toFinset, hfm, hmt, hft]

theorem zagMarkedTriple_ext {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {m m' : ZagMarkedTriple e π}
    (hfirst : m.first = m'.first) (hmiddle : m.middle = m'.middle)
    (hthird : m.third = m'.third) : m = m' := by
  cases m
  cases m'
  simp_all

end MetaMathlibExt
