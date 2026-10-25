import Mathlib
import sympy.Basic
import Instance.Combinatorics.ConsecutiveCyclicPrimeLabeling.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[cyclicLabel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
lemma cyclicLabel_pos
  {n offset : ℕ}
  {i : Fin (2 * n)} :
-- imply
  1 ≤ cyclicLabel n offset i := by
-- proof
  unfold cyclicLabel
  exact Nat.succ_pos _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cyclicLabel_le_size](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
lemma cyclicLabel_le_size
  {n offset : ℕ}
  {i : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  cyclicLabel n offset i ≤ 2 * n := by
-- proof
  unfold cyclicLabel
  have hpos : 0 < 2 * n := Nat.mul_pos (by decide) hn
  have hmod := Nat.mod_lt (i.val + offset) hpos
  exact Nat.succ_le_of_lt hmod

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cyclicLabel_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
lemma cyclicLabel_mem_range
  {n offset : ℕ}
  {i : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  1 ≤ cyclicLabel n offset i ∧ cyclicLabel n offset i ≤ 2 * n :=
-- proof
  ⟨cyclicLabel_pos n offset i, cyclicLabel_le_size n offset hn i⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cyclicLabel_zero_offset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean)
-/
@[path]
lemma cyclicLabel_zero_offset_zero
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  cyclicLabel n 0 ⟨0, Nat.mul_pos (by decide) hn⟩ = 1 := by
-- proof
  unfold cyclicLabel
  simp

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
