/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part2


namespace AlgebraicMatroidTest

noncomputable def testMatroidTrans : Matroid (RatFunc (ZMod 2)) :=
  (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).comapOn Set.univ id

end AlgebraicMatroidTest
