/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
import Instance.v1.Atlas.EllipticCurves.code.EndomorphismNorm.Part2
open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

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

end PositiveDefiniteInvolutionAlgebra
