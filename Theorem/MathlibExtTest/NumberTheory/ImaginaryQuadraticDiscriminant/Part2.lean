/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/


import Def.NumberTheory.ImaginaryQuadraticDiscriminant.Part2
import Lemma.Nat.ImaginaryQuadraticDiscriminant
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.NumberTheory.ImaginaryQuadraticDiscriminant
set_option autoImplicit false

/-! Tests for the canonical imaginary quadratic discriminant API. -/


namespace ImaginaryQuadraticDiscriminant

/-- Projection: `u = 2`. -/
example : decomp_neg_twelve.u = (2 : Int) := rfl

/-- Projection: `D_K = -3`. -/
example : decomp_neg_twelve.D_K = (-3 : Int) := rfl

/-- The packaged equation projects back to `-12 = u ^ 2 * D_K`. -/
example : (-12 : Int) = decomp_neg_twelve.u ^ 2 * decomp_neg_twelve.D_K :=
  decomp_neg_twelve.prop_eq

/-- The conductor remains normalized by `u ≥ 1`. -/
example : decomp_neg_twelve.u ≥ 1 :=
  decomp_neg_twelve.u_ge_one

/-- The fundamental factor remains fundamental in the canonical sense. -/
example : MetaMathlibExt.IsFundamentalDiscriminant decomp_neg_twelve.D_K :=
  isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant
    decomp_neg_twelve.isFundamental

/-- Consequently, `-12` is not fundamental imaginary. -/
example : ¬ IsFundamentalImaginaryQuadraticDiscriminant (-12 : Int) := by
  rintro ⟨_, hcan⟩
  exact not_fund_neg_twelve_canonical hcan

end ImaginaryQuadraticDiscriminant
