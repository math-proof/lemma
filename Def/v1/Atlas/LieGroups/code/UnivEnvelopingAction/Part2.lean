/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/UnivEnvelopingAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.SmoothVectors
public import Theorem.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
public import Theorem.Complex.IsStronglyContinuousToMonoidHom
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Abbrev.v1.Atlas.LieGroups.code.UnivEnvelopingAction

@[expose] public section

noncomputable section

namespace UnivEnvelopingAction

def ActsByScalar {V : Type*} [AddCommGroup V] [Module R V]
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V)
    (z : UniversalEnvelopingAlgebra R L) (c : R) : Prop :=
  φ z = c • LinearMap.id

end UnivEnvelopingAction
end
