/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Instance.MathlibExtTest.Combinatorics.Matroid.Algebraic


namespace AlgebraicMatroidTest

def testMatroid : Matroid ℚ :=
  (AlgebraicIndependent.matroid ℚ ℚ).comapOn Set.univ id

end AlgebraicMatroidTest
