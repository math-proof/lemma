/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/

module

public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Instance.MathlibExtTest.Combinatorics.Matroid.Algebraic

@[expose] public section

namespace AlgebraicMatroidTest

def testMatroid : Matroid ℚ :=
  (AlgebraicIndependent.matroid ℚ ℚ).comapOn Set.univ id

end AlgebraicMatroidTest
