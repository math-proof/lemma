import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.ConsecutiveCyclicPrimeLabeling
open MetaMathlibExt


/--
[cyclicLabel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
private lemma cyclicLabel_pos_eq
  {n offset : ℕ}
  {i : Fin (2 * n)} :
-- imply
  1 ≤ cyclicLabel n offset i := by
-- proof
  apply MetaMathlibExt.cyclicLabel_pos n offset i

/--
[cyclicLabel_le_size](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
private lemma cyclicLabel_le_size_eq
  {n offset : ℕ}
  {i : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  cyclicLabel n offset i ≤ 2 * n := by
-- proof
  apply MetaMathlibExt.cyclicLabel_le_size n offset hn i

/--
[cyclicLabel_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
private lemma cyclicLabel_mem_range_eq
  {n offset : ℕ}
  {i : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  1 ≤ cyclicLabel n offset i ∧ cyclicLabel n offset i ≤ 2 * n := by
-- proof
  apply MetaMathlibExt.cyclicLabel_mem_range n offset hn i

/--
[cyclicLabel_zero_offset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
private lemma cyclicLabel_zero_offset_zero_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  cyclicLabel n 0 ⟨0, Nat.mul_pos (by decide) hn⟩ = 1 := by
-- proof
  apply MetaMathlibExt.cyclicLabel_zero_offset_zero n hn


-- created on 2026-10-20
