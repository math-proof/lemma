module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part3
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice

def fkRectCoordinateCycleGraph (R : FKRectTorus) :
    SimpleGraph R.Vertex :=
  cycleGraph R.width □ cycleGraph R.height

end StatMech.FrontierD
