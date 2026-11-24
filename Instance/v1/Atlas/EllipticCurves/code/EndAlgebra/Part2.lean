module
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RingInvo
public import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
public import Structure.v1.Atlas.EllipticCurves.code.EndAlgebra.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section Definition121

namespace RingInvolution

variable {R : Type*} [Ring R]

/-- `RingInvolution R` is a `FunLike` type: it coerces to its underlying function and the
coercion is injective. -/
instance : FunLike (RingInvolution R) R R where
  coe φ := φ.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _, _, _⟩, _⟩ := f
    obtain ⟨⟨_, _, _, _⟩, _⟩ := g
    congr

end RingInvolution
end Definition121
