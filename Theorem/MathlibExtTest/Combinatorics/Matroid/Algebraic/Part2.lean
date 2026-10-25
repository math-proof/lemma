/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part2


namespace AlgebraicMatroidTest

example : Matroid.IsAlgebraicOver ℚ testMatroid :=
  repId.toIsAlgebraicOver

example : Matroid.IsAlgebraic testMatroid :=
  repSomeId.toIsAlgebraic

example : testMatroid =
    (AlgebraicIndependent.matroid ℚ ℚ).comapOn testMatroid.E repId.realize :=
  repId.matroid_eq

end AlgebraicMatroidTest
