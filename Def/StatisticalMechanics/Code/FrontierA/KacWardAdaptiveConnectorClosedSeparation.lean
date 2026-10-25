/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealPlacement


namespace StatMech.FrontierA

open Set

def kwConnectorClosedPath (a c b : ℂ) : Set ℂ :=
  segment ℝ a c ∪ segment ℝ c b

end StatMech.FrontierA
