module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
public import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex
open Finset SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

abbrev FKIsingMedialVertex (P : PlanarZ2Subgraph) := P.G.edgeSet


abbrev FKIsingMedialDart (P : PlanarZ2Subgraph) :=
  FKIsingMedialVertex P × FKIsingMedialSide

end
end StatMech.Universality
