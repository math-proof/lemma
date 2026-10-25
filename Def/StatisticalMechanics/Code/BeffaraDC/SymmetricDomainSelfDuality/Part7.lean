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
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part2
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

noncomputable def mixedMass (D : SymmetricDomain) (q : Real)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Real :=
  FK.bcProb D.finiteGraph D.mixedWiring (selfDualPoint q) q omega


noncomputable def mixedConnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if D.MixedConnected omega then D.mixedMass q omega else 0


noncomputable def openConnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if D.OpenConnected omega then D.mixedMass q omega else 0


end SymmetricDomain
end
end BeffaraDC
end StatMech
