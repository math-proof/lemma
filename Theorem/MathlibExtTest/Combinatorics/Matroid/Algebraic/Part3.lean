module
public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/
namespace AlgebraicMatroidTest

theorem generates_id_trans :
    IntermediateField.adjoin (ZMod 2)
      ((id : RatFunc (ZMod 2) → RatFunc (ZMod 2)) '' testMatroidTrans.E) = ⊤ := by
  have hE : testMatroidTrans.E = Set.univ := rfl
  rw [hE, Set.image_id]
  exact IntermediateField.adjoin_univ (ZMod 2) (RatFunc (ZMod 2))

end AlgebraicMatroidTest
