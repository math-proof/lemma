/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part8


namespace StatMech

namespace Exact3D

noncomputable def freeSelectedPositiveSubcriticalCorrelationLengthFromMass
    (h : FreePositiveSubcriticalMassBridge) (β : ℝ) : ℝ :=
  (freeSelectedPositiveSubcriticalMass h β)⁻¹


end Exact3D
end StatMech
