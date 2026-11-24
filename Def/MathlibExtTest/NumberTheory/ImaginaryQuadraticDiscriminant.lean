module
public import Def.NumberTheory.ImaginaryQuadraticDiscriminant.Part2
public import Theorem.Nat.ImaginaryQuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Theorem.MathlibExtTest.NumberTheory.ImaginaryQuadraticDiscriminant
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/
/-! Tests for the canonical imaginary quadratic discriminant API. -/
namespace ImaginaryQuadraticDiscriminant

/-- The decomposition `-12 = 2 ^ 2 * (-3)`. -/
def decomp_neg_twelve : ImaginaryQuadraticDiscriminantDecomposition (-12 : Int) :=
  ⟨2, -3, by decide, fund_neg_three, by decide⟩

end ImaginaryQuadraticDiscriminant
