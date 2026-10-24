/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/DiagonalSumsOfARiordanOrTriangularArray.lean -/


import sympy.atlas.Combinatorics.Enumerative.DiagonalSumsOfARiordanOrTriangularArray

namespace MetaMathlibExt

example {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ → M) (n : ℕ) :
    diagonalSums a n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 ij.2 :=
  rfl

#print axioms diagonalSums

end MetaMathlibExt
