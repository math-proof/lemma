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
import Def.v1.Atlas.EllipticCurves.code.EndAlgebra


section Definition121

/-- A ring involution on `R`: a ring anti-homomorphism `R → R` that is its own inverse.
This is the second half of Definition 12.1 in Sutherland's *Elliptic Curves*. -/
structure RingInvolution (R : Type*) [Ring R] extends RingAntiHom R R where
  involution : ∀ x : R, toFun (toFun x) = x

end Definition121
