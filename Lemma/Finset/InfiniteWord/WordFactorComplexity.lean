import Mathlib
import sympy.Basic
import Def.Combinatorics.InfiniteWord.WordFactorComplexity
open MetaMathlibExt


namespace MetaMathlibExt

/--
[wordFactorComplexity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/WordFactorComplexity.lean)
-/
@[path]
lemma wordFactorComplexity_zero
  [Finite A]
  {w : ℕ → A} :
-- imply
  wordFactorComplexity w 0 = 1 := by
-- proof
  unfold wordFactorComplexity InfiniteWord.factorSet
  have hsingle : Set.range (InfiniteWord.factor w 0) =
    {InfiniteWord.factor w 0 0} := by
    ext f
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨i, rfl⟩ := h
      exact funext fun j => nomatch j
    · intro h
      rw [h]
      exact ⟨0, rfl⟩
  rw [hsingle, Set.ncard_singleton]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
