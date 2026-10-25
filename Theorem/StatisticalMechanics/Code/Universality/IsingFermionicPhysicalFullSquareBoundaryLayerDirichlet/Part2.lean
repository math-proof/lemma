/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexDirichlet_harmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedHarmonicOn (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexDirichlet n hn) :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexGhostPrimitive n hn))).1

theorem vertexDirichlet_boundary
    (n : Nat) (hn : 0 < n) (x : Option (FKIsingSquareFullVertexNode n))
    (hx : vertexDirichletBoundary n x) :
    vertexDirichlet n hn x = vertexGhostPrimitive n hn x :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexGhostPrimitive n hn))).2 x hx


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
