module
public import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
public import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

/-- The absolute Galois group `AbsGaloisGroup k` is a group under composition. -/
noncomputable instance AbsGaloisGroup.instGroup (k : Type u) [Field k] :
    Group (AbsGaloisGroup k) :=
  inferInstance

end
