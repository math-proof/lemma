/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Group
public import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part4

@[expose] public section


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A pair of opposite flags is a "covering" pair when `F` is nonempty and its top
space is all of `V`. -/
def Flag.IsCoveringOppositePair (F F' : Flag k V) (_ : Flag.isOppositeFlag F F') : Prop :=
  ∃ (hlen : 0 < F.len), F.spaces ⟨F.len - 1, by omega⟩ = ⊤

end GeometricAlgebra
