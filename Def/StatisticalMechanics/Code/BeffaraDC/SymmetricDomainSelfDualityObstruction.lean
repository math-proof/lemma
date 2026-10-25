/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

def degenerateSite : Site 2 := ![0, 0]


def degenerateWalk : LatticePath degenerateSite degenerateSite :=
  SimpleGraph.Walk.nil


def degenerateSymmetricDomain : SymmetricDomain where
  u₁ := degenerateSite
  v₁ := degenerateSite
  u₂ := degenerateSite
  v₂ := degenerateSite
  γ₁ := degenerateWalk
  γ₂ := degenerateWalk
  isSymm := by
    simp [IsSymmetricPair, degenerateWalk, degenerateSite, diagReflFun]
  G := {degenerateSite}
  finite := Set.finite_singleton degenerateSite
  γ₁_subset := by simp [degenerateWalk]
  γ₂_subset := by simp [degenerateWalk]
  G_symm := by
    simp [degenerateSite, diagReflFun]


end
end SymmetricDomain
end BeffaraDC
end StatMech
