/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch


namespace StatMech.FrontierA

open Set

def kwIncomingPatchBase (v a : ℂ) (alpha : ℝ) : ℂ :=
  v + alpha * a

def kwIncomingPatchCorner (v a : ℂ) (alpha : ℝ) : ℂ :=
  v + alpha * kwVerticalPart a


def kwOutgoingPatchCorner (v b : ℂ) (beta : ℝ) : ℂ :=
  v + beta * kwHorizontalPart b

def kwOutgoingPatchEnd (v b : ℂ) (beta : ℝ) : ℂ :=
  v + beta * b


end StatMech.FrontierA
