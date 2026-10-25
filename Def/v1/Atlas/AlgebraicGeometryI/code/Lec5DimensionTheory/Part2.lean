/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec5DimensionTheory
set_option maxHeartbeats 400000


noncomputable section

open Set

/-- Promote an equivalence between two `T1` spaces with the proper-closed-finite property to a
homeomorphism. -/
def Homeomorph.ofEquivProperClosedFinite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y]
    (hX : ProperClosedFinite X) (hY : ProperClosedFinite Y)
    (e : X ≃ Y) : X ≃ₜ Y :=
  { toEquiv := e
    continuous_toFun := continuous_of_injective_of_T1_properClosedFinite hY e.injective
    continuous_invFun := continuous_of_injective_of_T1_properClosedFinite hX e.symm.injective }

end
