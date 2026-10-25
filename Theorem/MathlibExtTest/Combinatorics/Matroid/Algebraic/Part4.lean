/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part4


namespace AlgebraicMatroidTest

example : Transcendental (ZMod 2) (RatFunc.X : RatFunc (ZMod 2)) :=
  RatFunc.transcendental_X

example : Matroid.IsAlgebraicOver (ZMod 2) testMatroidTrans :=
  repTrans.toIsAlgebraicOver

example : Matroid.IsAlgebraic testMatroidTrans :=
  repSomeTrans.toIsAlgebraic

example : testMatroidTrans =
    (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).comapOn
      testMatroidTrans.E repTrans.realize :=
  repTrans.matroid_eq

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : Field R.L :=
  inferInstance

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : Algebra K R.L :=
  inferInstance

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : FaithfulSMul K R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Field R.K :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Field R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Algebra R.K R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : FaithfulSMul R.K R.L :=
  inferInstance

end AlgebraicMatroidTest
