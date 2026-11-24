module
public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/
namespace AlgebraicMatroidTest

noncomputable def testMatroidTrans : Matroid (RatFunc (ZMod 2)) :=
  (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).comapOn Set.univ id

end AlgebraicMatroidTest
