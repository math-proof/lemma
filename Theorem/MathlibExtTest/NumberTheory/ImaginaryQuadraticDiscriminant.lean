/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/


import Def.NumberTheory.ImaginaryQuadraticDiscriminant.Part2
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

end ImaginaryQuadraticDiscriminant
