/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

def mixedWiring (D : SymmetricDomain) : SimpleGraph D.Vertex :=
  StatMech.Lattice.boundaryCliqueGraph D.OnGammaOne ⊔
    StatMech.Lattice.boundaryCliqueGraph D.OnGammaTwo

end SymmetricDomain
end
end BeffaraDC
end StatMech
