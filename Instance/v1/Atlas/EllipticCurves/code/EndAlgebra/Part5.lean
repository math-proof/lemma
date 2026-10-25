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
import Def.v1.Atlas.EllipticCurves.code.EndAlgebra.Part4
universe u

open scoped TensorProduct


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

section EndomorphismAlgebra

variable (E : WeierstrassCurve.Affine F)

/-- The additive group structure on the endomorphism algebra, inherited from its ring
structure. -/
noncomputable instance EndomorphismAlgebra.instAddCommGroup :
    AddCommGroup (EndomorphismAlgebra E) :=
  (EndomorphismAlgebra.instRing E).toAddCommGroup

end EndomorphismAlgebra
end WeierstrassCurve.Affine
