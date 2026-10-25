/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/UnivEnvelopingAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Killing
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Def.v1.Atlas.LieGroups.code.UnivEnvelopingAction.Part3


noncomputable section

section CenterActsByScalar

variable (R : Type*) [Field R] [IsAlgClosed R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

structure IsKillingDualBasis (b d : ι → L) : Prop where
  orthonormal : ∀ i j : ι, killingForm R L (b i) (d j) = if i = j then 1 else 0
  expand_b : ∀ y : L, y = ∑ i : ι, (killingForm R L y (d i)) • (b i)
  expand_d : ∀ y : L, y = ∑ i : ι, (killingForm R L (b i) y) • (d i)

end CenterActsByScalar
end
