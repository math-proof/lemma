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
import Instance.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part4
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

def MixedConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Prop :=
  ∃ x y : D.Vertex,
    D.OnGammaOne x ∧ D.OnGammaTwo y ∧
      (FK.openSub D.finiteGraph omega ⊔ D.mixedWiring).Reachable x y

end SymmetricDomain
end
end BeffaraDC
end StatMech
