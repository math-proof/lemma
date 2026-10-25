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
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part4
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

structure MixedDualComplementRN (D : SymmetricDomain) (q : Real) where
  dual : ConfigSpace (Sym2 D.Vertex) ≃ ConfigSpace (Sym2 D.Vertex)
  connected_dual_iff : ∀ omega,
    D.MixedConnected (dual omega) ↔ ¬D.MixedConnected omega
  rn_upper : ∀ eta,
    D.mixedMass q (dual.symm eta) ≤ q ^ 2 * D.mixedMass q eta


end SymmetricDomain
end
end BeffaraDC
end StatMech
