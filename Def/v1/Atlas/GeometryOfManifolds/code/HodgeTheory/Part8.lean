/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part8
set_option autoImplicit false

open DifferentialFormSpace


/-- The left smoothing remainder $S_{\text{left}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sLeftLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : E →ₗ[ℝ] E :=
  h.S_left.toLinearMap

/-- The right smoothing remainder $S_{\text{right}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sRightLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : F →ₗ[ℝ] F :=
  h.S_right.toLinearMap

