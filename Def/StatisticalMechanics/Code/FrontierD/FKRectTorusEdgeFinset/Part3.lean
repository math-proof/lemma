module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectFinsetClusterCount (R : FKRectTorus)
    (F : Finset R.EdgeIndex) : Nat :=
  fkRectNumClusters R (fkRectConfigurationOfEdges R F)

end
end StatMech.FrontierD
