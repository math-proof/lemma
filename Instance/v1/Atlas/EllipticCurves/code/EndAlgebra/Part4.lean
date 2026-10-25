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
import Def.v1.Atlas.EllipticCurves.code.EndAlgebra.Part3
universe u

open scoped TensorProduct


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

section EndomorphismAlgebra

variable (E : WeierstrassCurve.Affine F)

/-- The endomorphism algebra also inherits a `ℤ`-algebra structure. -/
noncomputable instance EndomorphismAlgebra.instAlgebraInt :
    Algebra ℤ (EndomorphismAlgebra E) :=
  inferInstance

/-- The endomorphism algebra is a `ℚ`-module via its `ℚ`-algebra structure. -/
noncomputable instance EndomorphismAlgebra.instModule :
    Module ℚ (EndomorphismAlgebra E) :=
  (EndomorphismAlgebra.instAlgebra E).toModule

end EndomorphismAlgebra
end WeierstrassCurve.Affine
