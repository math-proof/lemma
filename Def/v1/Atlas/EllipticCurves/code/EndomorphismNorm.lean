/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
import Abbrev.v1.Atlas.EllipticCurves.code.EndomorphismNorm
open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

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

end PositiveDefiniteInvolutionAlgebra
