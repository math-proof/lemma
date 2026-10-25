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
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part6
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

def overlappingSingletonDomain : SymmetricDomain where
  u₁ := ![0, 0]
  v₁ := ![0, 0]
  u₂ := ![0, 0]
  v₂ := ![0, 0]
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair]
  G := {![0, 0]}
  finite := Set.finite_singleton _
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    simp [diagReflFun_apply]


end SymmetricDomain
end
end BeffaraDC
end StatMech
