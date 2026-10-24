/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.EndAlgClassification
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification

open scoped TensorProduct

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- A nontrivial PD-involution algebra has no zero divisors: if `a * b = 0`
then `a = 0` or `b = 0`. Proved using positive-definiteness of the norm. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero [Nontrivial A] (a b : A) (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have hNb_ne : normMap b ≠ 0 := ne_of_gt (normMap_pos b hb)
  have h1 : a * (b * invol b) = 0 := by rw [← mul_assoc, hab, zero_mul]
  rw [normMap_spec b, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  have h2 : a = (normMap b)⁻¹ • (normMap b • a) := by rw [inv_smul_smul₀ hNb_ne]
  rw [h1, smul_zero] at h2
  exact ha h2

/-- A nontrivial PD-involution algebra has no zero divisors. -/
instance instNoZeroDivisors [Nontrivial A] : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := eq_zero_or_eq_zero_of_mul_eq_zero a b hab

/-- A nontrivial PD-involution algebra is an integral domain. -/
instance instIsDomain [Nontrivial A] : IsDomain A :=
  NoZeroDivisors.to_isDomain A

/-- The rational endomorphism algebra `End⁰(E) = End(E) ⊗_ℤ ℚ` of an elliptic
curve `E`, an abbreviation for `EndomorphismAlgebra E`. -/
abbrev End0 := EndomorphismAlgebra E

/-- The Rosati dual / canonical involution of an element of `End⁰(E)`,
obtained from the PD-involution algebra structure on the endomorphism algebra. -/
noncomputable def End0.dual (α : End0 E) : End0 E :=
  @PositiveDefiniteInvolutionAlgebra.invol (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

/-- The reduced norm `N : End⁰(E) → ℚ` of an endomorphism, obtained from the
PD-involution algebra structure on `End⁰(E)`. Geometrically this is the
degree of an isogeny (extended ℚ-linearly). -/
noncomputable def End0.N (α : End0 E) : ℚ :=
  @PositiveDefiniteInvolutionAlgebra.normMap (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

/-- The endomorphism algebra `End⁰(E)` is nontrivial (contains both `0` and `1`). -/
noncomputable instance End0.instNontrivial :
    letI := EndomorphismAlgebra.instRing E; Nontrivial (End0 E) :=
  letI := EndomorphismAlgebra.instRing E
  _root_.WeierstrassCurve.Affine.EndomorphismAlgebra.instNontrivial E

/-- The reduced trace `T : End⁰(E) → ℚ` of an endomorphism, obtained from the
PD-involution structure on `End⁰(E)`. -/
noncomputable def End0.T (α : End0 E) : ℚ :=
  @PositiveDefiniteInvolutionAlgebra.traceMap (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

end WeierstrassCurve.Affine

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The characteristic polynomial of an endomorphism `α`, as the polynomial
`X² - T(α) X + N(α) ∈ ℚ[X]`. -/
noncomputable def End0.charPolyOf (α : End0 E) : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C (End0.T E α) * Polynomial.X + Polynomial.C (End0.N E α)
