/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ComplementarySequenceDeterminedBySubsequenceSumEquation.lean -/


import sympy.atlas.NumberTheory.ComplementarySequenceDeterminedBySubsequenceSumEquation

namespace MetaMathlibExt

example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) (n : ℕ) : 0 < a n := h.1 n
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) (n : ℕ) : 0 < b n := h.2.1 n
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) : StrictMono a := h.2.2.1
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) : StrictMono b := h.2.2.2.1

#print axioms IsComplementaryPair
#print axioms SatisfiesParametrizedSumEquation

end MetaMathlibExt
