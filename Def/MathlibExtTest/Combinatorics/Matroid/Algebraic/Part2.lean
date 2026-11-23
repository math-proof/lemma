/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/

module

public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic

@[expose] public section

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
