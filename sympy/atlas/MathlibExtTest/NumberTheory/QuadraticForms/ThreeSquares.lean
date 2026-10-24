/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QuadraticForms/ThreeSquares.lean -/


import sympy.atlas.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares

namespace Nat

example : threeSquareRepresentationCount 0 = 1 := by decide

example : threeSquareRepresentationCount 1 = 6 := by decide

example : threeSquareRepresentationCount 7 = 0 :=
  threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven 7 (by decide) (by decide)

example : threeSquareRepresentationCount 4 = threeSquareRepresentationCount 1 :=
  threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four 4
    (by decide) (by decide)

#print axioms Nat.threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven
#print axioms Nat.threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four

end Nat
