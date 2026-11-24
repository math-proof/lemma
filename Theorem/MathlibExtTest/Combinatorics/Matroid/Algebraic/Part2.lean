module
public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/
namespace AlgebraicMatroidTest

example : Matroid.IsAlgebraicOver ℚ testMatroid :=
  repId.toIsAlgebraicOver

example : Matroid.IsAlgebraic testMatroid :=
  repSomeId.toIsAlgebraic

example : testMatroid =
    (AlgebraicIndependent.matroid ℚ ℚ).comapOn testMatroid.E repId.realize :=
  repId.matroid_eq

end AlgebraicMatroidTest
