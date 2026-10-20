/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/WordFactorComplexity.lean -/

import sympy.atlas.Combinatorics.InfiniteWord.Factor
import Mathlib.Data.Set.Card

namespace MetaMathlibExt

/-- Factor complexity of an infinite word `w` over a finite alphabet:
the complexity function `p_w(n)`, the number of distinct contiguous factors
of `w` of length `n`, where a length-`n` factor starting at `i` is
`fun j : Fin n => w (i + j)`. The image set collapses repeated occurrences,
so `Set.ncard` of the range counts distinct factors rather than occurrences.

Source: Fabien Durand, Julien Leroy, and Gwenaël Richomme, *Do the
Properties of an S-adic Representation Determine Factor Complexity?*,
Journal of Integer Sequences 16 (2013), Article 13.2.6, complexity-function
definition, lines 117–128,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>. -/
noncomputable def wordFactorComplexity {A : Type*} [Finite A]
    (w : ℕ → A) (n : ℕ) : ℕ :=
  Set.ncard (InfiniteWord.factorSet w n)

/-- Boundary value: there is exactly one length-`0` factor. -/
theorem wordFactorComplexity_zero {A : Type*} [Finite A]
    (w : ℕ → A) : wordFactorComplexity w 0 = 1 := by
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
