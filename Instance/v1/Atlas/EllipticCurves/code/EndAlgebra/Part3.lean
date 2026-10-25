/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.RingInvo
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Abbrev.v1.Atlas.EllipticCurves.code.EndAlgebra
universe u

open scoped TensorProduct


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

section EndomorphismAlgebra

variable (E : WeierstrassCurve.Affine F)

/-- The endomorphism algebra `End(E) ⊗_ℤ ℚ` inherits a ring structure from the tensor
product of rings. -/
noncomputable instance EndomorphismAlgebra.instRing : Ring (EndomorphismAlgebra E) :=
  inferInstance

/-- The endomorphism algebra `End(E) ⊗_ℤ ℚ` is naturally a `ℚ`-algebra via the right tensor
factor. -/
noncomputable instance EndomorphismAlgebra.instAlgebra :
    Algebra ℚ (EndomorphismAlgebra E) :=
  Algebra.TensorProduct.rightAlgebra

end EndomorphismAlgebra
end WeierstrassCurve.Affine
