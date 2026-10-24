/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/WordFactorComplexity.lean -/


import sympy.atlas.Combinatorics.InfiniteWord.WordFactorComplexity
import Lemma.Finset.InfiniteWord.WordFactorComplexity

open MetaMathlibExt

/-- Regression: a constant binary word has exactly one factor of each length. -/
example : wordFactorComplexity (fun _ : ℕ => false) 2 = 1 := by
  unfold wordFactorComplexity
  have hsingle : InfiniteWord.factorSet (fun _ : ℕ => false) 2 = {fun _ => false} := by
    ext f
    simp only [InfiniteWord.factorSet, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      funext j
      rfl
    · intro h
      rw [h]
      exact ⟨0, rfl⟩
  rw [hsingle, Set.ncard_singleton]

example (w : ℕ → Bool) : wordFactorComplexity w 0 = 1 :=
  wordFactorComplexity_zero w
