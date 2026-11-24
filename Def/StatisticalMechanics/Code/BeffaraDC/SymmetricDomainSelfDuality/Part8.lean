module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part3
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

noncomputable def mixedDisconnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if ¬D.MixedConnected omega then D.mixedMass q omega else 0


end SymmetricDomain
end
end BeffaraDC
end StatMech
