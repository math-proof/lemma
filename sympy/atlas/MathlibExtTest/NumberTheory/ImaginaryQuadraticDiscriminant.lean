/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/


import sympy.atlas.NumberTheory.ImaginaryQuadraticDiscriminant
import Lemma.Nat.ImaginaryQuadraticDiscriminant
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-! Tests for the canonical imaginary quadratic discriminant API. -/

namespace ImaginaryQuadraticDiscriminant

/-- The canonical fundamental-discriminant predicate holds for `-3`. -/
theorem fund_neg_three_canonical :
    MetaMathlibExt.IsFundamentalDiscriminant (-3 : Int) := by
  unfold MetaMathlibExt.IsFundamentalDiscriminant
  left
  refine ⟨?_, by decide⟩
  exact ((Int.prime_iff_natAbs_prime (k := -3)).mpr
    (by simpa using Nat.prime_three)).squarefree

/-- `-3` is a fundamental imaginary quadratic discriminant. -/
theorem fund_neg_three :
    IsFundamentalImaginaryQuadraticDiscriminant (-3 : Int) :=
  isFundamentalImaginaryQuadraticDiscriminant_mk (by decide) fund_neg_three_canonical

/-- The wrapper projects to the canonical predicate. -/
example : MetaMathlibExt.IsFundamentalDiscriminant (-3 : Int) :=
  isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant fund_neg_three

/-- A fundamental imaginary discriminant is imaginary. -/
example : IsImaginaryQuadraticDiscriminant (-3 : Int) :=
  isFundamentalImaginaryQuadraticDiscriminant_isImaginary fund_neg_three

/-- Membership in the imaginary-discriminant set. -/
example : (-3 : Int) ∈ imaginaryQuadraticDiscriminants :=
  mem_neg_three

/-- Membership in the fundamental-imaginary-discriminant set. -/
example : (-3 : Int) ∈ fundamentalImaginaryQuadraticDiscriminants :=
  fund_neg_three

/-- The imaginary-discriminant iff helper exposes the exact congruence condition. -/
example : (-3 : Int) < 0 ∧ ((-3 : Int) % 4 = 0 ∨ (-3 : Int) % 4 = 1) :=
  (isImaginaryQuadraticDiscriminant_iff _).mp mem_neg_three

/-- The decomposition `-12 = 2 ^ 2 * (-3)`. -/
def decomp_neg_twelve : ImaginaryQuadraticDiscriminantDecomposition (-12 : Int) :=
  ⟨2, -3, by decide, fund_neg_three, by decide⟩

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
