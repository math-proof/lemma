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
import Structure.v1.Atlas.EllipticCurves.code.EndAlgebra


section Definition121

namespace RingAntiHom

variable {R S : Type*} [Ring R] [Ring S]

/-- `RingAntiHom R S` is a `FunLike` type: it coerces to its underlying function and the
coercion is injective. -/
instance : FunLike (RingAntiHom R S) R S where
  coe := RingAntiHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

end RingAntiHom
end Definition121
