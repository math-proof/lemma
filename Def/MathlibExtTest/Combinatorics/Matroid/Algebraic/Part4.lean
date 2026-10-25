/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part3


namespace AlgebraicMatroidTest

noncomputable def repTrans :
    Matroid.AlgebraicRepresentation (ZMod 2) testMatroidTrans where
  L := RatFunc (ZMod 2)
  realize := id
  generates := generates_id_trans
  matroid_eq := rfl

noncomputable def repSomeTrans :
    Matroid.AlgebraicRepresentationSomeField testMatroidTrans where
  K := ZMod 2
  L := RatFunc (ZMod 2)
  realize := id
  generates := generates_id_trans
  matroid_eq := rfl

end AlgebraicMatroidTest
