module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareFullVertexNode (n : Nat) :=
  (fkSquareBoxPlanar n).V

abbrev FKIsingSquareFullFaceNode (n : Nat) :=
  FKIsingSquareInteriorCell n


end
end StatMech.Universality
