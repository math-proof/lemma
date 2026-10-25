/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector


namespace StatMech.FrontierA

open Set


def kwConnectorOpenPath (a c b : ℂ) : Set ℂ :=
  {z : ℂ | Sbtw ℝ a z c} ∪ {z : ℂ | Sbtw ℝ c z b}


end StatMech.FrontierA
