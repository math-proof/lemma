module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareFullRadialNode (n : Nat) :=
  FKIsingSquareFullVertexNode n ⊕ FKIsingSquareFullFaceNode n

end
end StatMech.Universality
