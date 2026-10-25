/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic


namespace AlgebraicMatroidTest

def repId : Matroid.AlgebraicRepresentation ℚ testMatroid where
  L := ℚ
  realize := id
  generates := generates_id
  matroid_eq := rfl

def repSomeId : Matroid.AlgebraicRepresentationSomeField testMatroid where
  K := ℚ
  L := ℚ
  realize := id
  generates := generates_id
  matroid_eq := rfl

end AlgebraicMatroidTest
