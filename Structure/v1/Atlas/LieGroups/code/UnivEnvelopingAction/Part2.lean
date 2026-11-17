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
public import Def.v1.Atlas.LieGroups.code.UnivEnvelopingAction.Part3


public noncomputable section

section CenterActsByScalar

variable (R : Type*) [Field R] [IsAlgClosed R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

structure IsKillingDualBasis (b d : ι → L) : Prop where
  orthonormal : ∀ i j : ι, killingForm R L (b i) (d j) = if i = j then 1 else 0
  expand_b : ∀ y : L, y = ∑ i : ι, (killingForm R L y (d i)) • (b i)
  expand_d : ∀ y : L, y = ∑ i : ι, (killingForm R L (b i) y) • (d i)

end CenterActsByScalar
end
