/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Structure.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


def leftCriticalInterval (S : IsingRGCoordinateScaffold C) : Set ℝ :=
  Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3)

end IsingRGCoordinateScaffold
end Exact3D
end StatMech
