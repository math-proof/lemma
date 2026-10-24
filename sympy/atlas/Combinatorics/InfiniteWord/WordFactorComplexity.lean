/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/WordFactorComplexity.lean -/

import sympy.atlas.Combinatorics.InfiniteWord.Factor
import Lemma.Finset.InfiniteWord.Factor
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
end MetaMathlibExt
