/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Def.MathlibExtTest.Combinatorics.Matroid.Algebraic


namespace AlgebraicMatroidTest

theorem generates_id :
    IntermediateField.adjoin ℚ ((id : ℚ → ℚ) '' Set.univ) = ⊤ := by
  rw [Set.image_id]
  exact IntermediateField.adjoin_univ ℚ ℚ

end AlgebraicMatroidTest
