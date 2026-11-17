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
public import Structure.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics

@[expose] public section

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace Flag

/-- The type of a flag `F` is the sequence of dimensions of its constituent
submodules. -/
noncomputable def type (F : Flag k V) : Fin F.len → ℕ :=
  fun i => Module.finrank k (F.spaces i)

/-- Two flags have the same type when they have the same length and the same
sequence of dimensions. -/
def sameType (F₁ F₂ : Flag k V) : Prop :=
  F₁.len = F₂.len ∧ ∀ (h : F₁.len = F₂.len) (i : Fin F₁.len),
    F₁.type i = F₂.type (i.cast h)


end Flag
end GeometricAlgebra
