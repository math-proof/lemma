/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part10


namespace StatMech

namespace Exact3D

noncomputable def freeSelectedPositiveSubcriticalCorrelationLength
    (h : FreePositiveSubcriticalCorrelationLengthBridge) (β : ℝ) : ℝ :=
  if hβpos : 0 < β then
    if hβc : β < Ising.betaC 3 then Classical.choose (h β hβpos hβc)
    else 0
  else 0


end Exact3D
end StatMech
