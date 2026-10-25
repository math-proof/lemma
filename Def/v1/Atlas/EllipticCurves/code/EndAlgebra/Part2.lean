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
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part2


section Definition121

namespace RingInvolution

variable {R : Type*} [Ring R]

/-- Convert Mathlib's `RingInvo R` (a ring involution as a `R →+* Rᵐᵒᵖ`) to a
`RingInvolution R`. -/
def ofRingInvo (f : RingInvo R) : RingInvolution R where
  toFun r := (f r).unop
  map_add a b := by simp [_root_.map_add]
  map_one := by simp [_root_.map_one]
  map_mul_rev a b := by simp [_root_.map_mul, MulOpposite.unop_mul]
  involution x := f.involution x

end RingInvolution
end Definition121
