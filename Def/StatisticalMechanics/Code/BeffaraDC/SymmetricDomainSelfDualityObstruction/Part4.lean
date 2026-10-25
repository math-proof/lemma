/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part3
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

def connectedBridgeSite : Site 2 := ![0, 0]

end
end SymmetricDomain
end BeffaraDC
end StatMech
