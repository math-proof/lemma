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


section Definition121

/-- A ring anti-homomorphism `R → S`: a map that preserves addition and the multiplicative
identity, but reverses the order of multiplication, i.e. `f (a * b) = f b * f a`.
Corresponds to Definition 12.1 of Sutherland's *Elliptic Curves*. -/
structure RingAntiHom (R S : Type*) [Ring R] [Ring S] where
  toFun : R → S
  map_add : ∀ a b : R, toFun (a + b) = toFun a + toFun b
  map_one : toFun 1 = 1
  map_mul_rev : ∀ a b : R, toFun (a * b) = toFun b * toFun a

end Definition121
