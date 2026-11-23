/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/
module

public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod
public import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic

public section

namespace AlgebraicMatroidTest

theorem generates_id :
    IntermediateField.adjoin ℚ ((id : ℚ → ℚ) '' Set.univ) = ⊤ := by
  rw [Set.image_id]
  exact IntermediateField.adjoin_univ ℚ ℚ

end AlgebraicMatroidTest
