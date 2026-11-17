/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/UnivEnvelopingAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.SmoothVectors
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Structure.v1.Atlas.LieGroups.code.UnivEnvelopingAction

@[expose] public section

noncomputable section

namespace UnivEnvelopingAction

def InfinitesimalCharacter.apply (χ : InfinitesimalCharacter R L) (z : CenterUEA R L) : R :=
  χ.toAlgHom z

end UnivEnvelopingAction
end
