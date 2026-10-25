/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSameEdge.Part2


namespace StatMech.FrontierA

open Set

def kwTranslatedOpenRayTail (v a : ℂ) : Set ℂ :=
  {z | ∃ t : ℝ, 1 < t ∧ z = v + t * a}

end StatMech.FrontierA
